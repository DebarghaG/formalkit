"""Propose, check, learn from the failure: CEGIS, constructions, candidate pools, assumptions."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Sequence

from formalkit.agent import Step
from formalkit.client import Backend
from formalkit.core import Result, Verdict
from formalkit.llm import LLM, extract_code


@dataclass
class Loop:
    """The outcome of :func:`cegis`, :func:`propose_until_proved` and :func:`assume_and_discharge`."""

    candidate: Any  # the accepted candidate, or None
    steps: list[Step] = field(default_factory=list)  # every candidate and its verdict

    @property
    def ok(self) -> bool:
        return self.candidate is not None


def cegis(
    propose: Callable[[list[Step]], Any],
    verify: Callable[[Any], Result],
    *,
    rounds: int = 10,
    accept: frozenset = frozenset({Verdict.PROVED}),
) -> Loop:
    """Counterexample-guided synthesis: propose, verify, learn from the counterexample.

    ``propose(history)`` returns the next candidate given every earlier
    attempt (each Step's ``result.counterexample`` / ``result.core`` says
    why it failed); ``verify(candidate)`` checks it. Stops when a verdict is
    in ``accept``. Also the shape of LLM-guided loop-invariant synthesis
    (generate, check with the verifier, feed errors back).
    """
    steps: list[Step] = []
    seen: dict[str, Result] = {}  # a repeated candidate is not re-verified
    for _ in range(rounds):
        candidate = propose(steps)
        if candidate is None:
            break
        key = str(candidate)
        result = seen[key] if key in seen else verify(candidate)
        seen[key] = result
        steps.append(Step(result.backend, {"code": key}, result))
        if result.verdict in accept:
            return Loop(candidate, steps)
    return Loop(None, steps)


def propose_until_proved(
    backend: Backend,
    problem: str,
    propose: Callable[[list[Step]], str | None],
    *,
    rounds: int = 5,
    timeout: float = 120,
) -> Loop:
    """Let the model add to a fixed problem until the engine decides it (AlphaGeometry).

    The engine does all deduction; the model only supplies what the engine
    cannot invent, such as auxiliary constructions. ``propose(history)``
    returns a new version of the problem (or None to stop) after an
    ``unknown``; any decisive verdict ends the loop.
    """
    steps: list[Step] = []
    seen: dict[str, Result] = {}  # a repeated proposal is not re-run
    current: str | None = problem
    for _ in range(rounds + 1):
        if current is None:
            break
        result = seen[current] if current in seen else backend.run(current, timeout=timeout)
        seen[current] = result
        steps.append(Step(backend.name, {"code": current}, result, backend))
        if result.decisive:
            return Loop(current if result.verdict is Verdict.PROVED else None, steps)
        current = propose(steps)
    return Loop(None, steps)


def ask_with_feedback(llm: LLM, task: str, *, keep: int = 6, **overrides: Any) -> Callable[[list[Step]], str]:
    """A ``propose`` for :func:`cegis` / :func:`propose_until_proved` / :func:`assume_and_discharge`:
    show the model the task plus its earlier attempts with their feedback, and take its next candidate.

    Only the last ``keep`` attempts are shown in full, so long loops do not
    outgrow the context window.
    """

    def propose(history: list[Step]) -> str:
        shown = history[-keep:] if keep else []
        first = len(history) - len(shown) + 1
        attempts = (f"\n\n({first - 1} earlier attempts omitted; all failed.)" if first > 1 else "") + "".join(
            f"\n\nAttempt {i}:\n```\n{s.arguments['code']}\n```\nResult:\n{s.result.feedback(2000)}"
            for i, s in enumerate(shown, first)
        )
        prompt = f"{task}{attempts}\n\nReply with your {'next' if history else 'first'} candidate in a single fenced code block."
        return extract_code(llm.ask(prompt, **overrides)[0])

    return propose


@dataclass
class Pruned:
    """The outcome of :func:`houdini`."""

    kept: list[str]  # the surviving candidates
    result: Result  # the verdict with exactly those candidates
    rounds: int

    @property
    def proved(self) -> bool:
        return self.result.verdict is Verdict.PROVED


def houdini(candidates: Sequence[str], check: Callable[[list[tuple[str, str]]], Result], *, rounds: int = 20) -> Pruned:
    """Houdini pruning over a pool of candidate conjuncts (Kamath et al., LaM4Inv).

    Pool candidate invariants from many samples; ``check`` receives
    ``(label, candidate)`` pairs, runs them all at once, and must report the
    labels of the failing candidates in ``result.core``. Failing ones are
    dropped until the rest are accepted together (a fixed point) or no
    blamed candidate is left to drop. Order candidates first (e.g. with a
    reranker, as in iRank) when checks are expensive.
    """
    pool = [(f"c{i}", c) for i, c in enumerate(dict.fromkeys(candidates))]
    result = Result(Verdict.UNKNOWN, "no candidates")
    for n in range(1, rounds + 1):
        result = check(pool)
        if result.verdict is Verdict.PROVED:
            return Pruned([c for _, c in pool], result, n)
        blamed = set(result.core) & {label for label, _ in pool}
        if not blamed:
            return Pruned([c for _, c in pool], result, n)
        pool = [(label, c) for label, c in pool if label not in blamed]
    return Pruned([c for _, c in pool], result, rounds)


def assume_and_discharge(
    propose: Callable[[list[Step]], str | None],
    prove_under: Callable[[str], Result],
    discharge: Callable[[str], Result],
    *,
    rounds: int = 5,
) -> Loop:
    """Lemur's proposal-check-repair calculus, with the verifier as the only authority.

    The model proposes an assumption ``a`` (e.g. a loop invariant). The goal
    is accepted only if both ``prove_under(a)`` - the property, assuming
    ``a`` - and ``discharge(a)`` - ``a`` itself - are PROVED. A failed side
    is fed back (its counterexample and core are in the history) and the
    model proposes again: repair and backtracking. Soundness rests on the
    two callables checking exactly those obligations.
    """
    steps: list[Step] = []
    for _ in range(rounds):
        assumption = propose(steps)
        if assumption is None:
            break
        under = prove_under(assumption)
        steps.append(Step(under.backend, {"code": assumption, "obligation": "goal under assumption"}, under))
        if under.verdict is not Verdict.PROVED:
            continue
        holds = discharge(assumption)
        steps.append(Step(holds.backend, {"code": assumption, "obligation": "assumption"}, holds))
        if holds.verdict is Verdict.PROVED:
            return Loop(assumption, steps)
    return Loop(None, steps)
