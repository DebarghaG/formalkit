"""Learning from formal feedback: data, rewards, curricula, expert iteration, evaluation.

formalkit is not a trainer. It is the environment and the labeller: every
checked attempt becomes data, and you plug in the training step.

    trace = formalkit.Trace()
    with formalkit.observe(trace):
        ...                                       # any patterns, agents, searches
    write_jsonl("tactics.jsonl", trace.tactics())      # step-level supervision, failures included
    write_jsonl("prefs.jsonl", trace.preferences())    # DPO pairs from compiler feedback

    groups = rollouts(llm, lean, problems, k=8)          # GRPO-style groups with checker rewards
    run = expert_iteration(problems, attempt, train=my_finetune, rounds=4)

What the learning-from-feedback literature trains on, and where it comes from:

=====================  ==================================================================
data                   source
=====================  ==================================================================
verified proofs        ``Trace.proofs()``, :func:`expert_iteration` (expert iteration,
                       synthetic-data engines)
(state, step, outcome) ``Trace.tactics()`` (tactic servers, failed search paths, Lean4trace)
preference pairs       ``Trace.preferences()`` (DPO on compiler-labelled state-tactic pairs)
repair triples         :func:`repair_pairs` on any attempt sequence (APRIL, self-correction)
prefix labels          :func:`prefix_labels` (process-supervised verifiers, FormL4's PSV)
rewarded rollouts      :func:`rollouts` with :data:`solved`, :func:`binary`, :func:`compiles` or custom rewards
                       (RL from proof-assistant feedback)
=====================  ==================================================================
"""

from __future__ import annotations

import json
import random
import threading
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping, Sequence

from formalkit.agent import Step
from formalkit.client import Backend
from formalkit.core import Result, Verdict
from formalkit.llm import LLM, extract_code
from formalkit.observe import BudgetExceeded
from formalkit.patterns.prove import error_lines

Reward = Callable[[Result], float]


def write_jsonl(path: str | Path, rows: Iterable[Mapping[str, Any]]) -> int:
    """Write rows as JSON lines; returns how many."""
    n = 0
    with open(path, "w") as f:
        for row in rows:
            f.write(json.dumps(row, default=str) + "\n")
            n += 1
    return n


# -- rewards -------------------------------------------------------------------------------


def binary(accept: Sequence[Verdict] = (Verdict.PROVED,)) -> Reward:
    """1 when the checker's verdict is in ``accept``, else 0 - the RLPAF / GRPO reward."""
    accepted = frozenset(accept)
    return lambda result: 1.0 if result.verdict in accepted else 0.0


solved = binary()  # 1 for a proof, else 0


def compiles(success: float = 1.0, valid: float = 0.2) -> Reward:
    """Partial credit: full reward on success (proved), some for input that at least checks."""
    return lambda r: success if r.verdict is Verdict.PROVED else valid if r.verdict is not Verdict.ERROR else 0.0


# -- rollouts ------------------------------------------------------------------------------


@dataclass
class Rollout:
    problem: str
    prompt: list[dict[str, Any]]  # the chat messages the model saw
    completion: str  # its raw reply
    code: str  # the formal artifact extracted from it
    result: Result
    reward: float


def rollouts(
    llm: LLM,
    backend: Backend,
    problems: Sequence[str],
    *,
    k: int = 8,
    reward: Reward = solved,
    instructions: str = "",
    pinned: bool = False,
    timeout: float = 120,
    **overrides: Any,
) -> list[list[Rollout]]:
    """``k`` checked, rewarded completions per problem: one group per problem, ready for GRPO.

    Rewards come only from the checker's verdict (via ``reward``), never
    from the model's own claims. With ``pinned=True`` each problem is a
    formal statement with one ``sorry`` and the model only fills the hole
    (:func:`~formalkit.patterns.pin`), so a reward is never earned by
    proving a different statement. ``overrides`` (e.g. ``temperature``) go
    to the model.
    """
    from formalkit.patterns.generate import _ask, challenge_input, pin, reply_inputs

    spec = backend.spec
    overrides.setdefault("temperature", 1.0)
    fills = {p: pin(p) for p in problems} if pinned else {}

    def one(problem: str) -> Rollout:
        task = "Prove this statement." if pinned else problem
        prompt = [
            {"role": "system", "content": f"You write {spec.language} for {spec.name}.\n\n{spec.describe()}"},
            {"role": "user", "content": "\n\n".join(x for x in (task, instructions) if x)
             + _ask(spec, problem if pinned else None)},
        ]  # fmt: skip
        completion = llm.chat(prompt, **dict(overrides))["content"]
        text, inputs = (extract_code(completion), {}) if pinned else reply_inputs(completion, spec)
        for code in fills[problem].variants(text) if pinned else [text]:
            result = backend.run(code, timeout=timeout, **inputs, **(challenge_input(backend, problem) if pinned else {}))
            if result.verdict is not Verdict.ERROR:
                break
        return Rollout(problem, prompt, completion, code, result, reward(result))

    def safe(problem: str) -> Rollout:
        try:
            return one(problem)
        except BudgetExceeded:
            raise
        except Exception as e:  # a failed rollout earns nothing, but the others still count
            failed = Result(Verdict.ERROR, f"rollout failed: {type(e).__name__}: {e}")
            return Rollout(problem, [], "", "", failed, 0.0)

    with ThreadPoolExecutor(8) as pool:
        flat = list(pool.map(safe, [p for p in problems for _ in range(k)]))
    return [flat[i * k : (i + 1) * k] for i in range(len(problems))]


def to_rl_rows(groups: Sequence[Sequence[Rollout]]) -> list[dict[str, Any]]:
    """Rollout groups as rows ``{"group", "prompt", "completion", "reward", "verdict"}``."""
    return [{"group": g, "prompt": r.prompt, "completion": r.completion, "reward": r.reward,
             "verdict": r.result.verdict.value} for g, group in enumerate(groups) for r in group]  # fmt: skip


# -- supervision from attempt sequences -------------------------------------------------------


def repair_pairs(steps: Sequence[Step], done: Callable[[Result], bool] = lambda r: r.verdict is Verdict.PROVED) -> list[dict[str, Any]]:
    """``{"broken", "diagnostics", "fixed"}`` triples from one attempt sequence (APRIL).

    Every failed attempt that precedes a successful one is paired with it:
    the broken input, what the checker said, and the input that worked.
    Feed any sequence of attempts: ``refine``, ``repair``, an Agent's steps.
    """
    pairs, pending = [], []
    for step in steps:
        if done(step.result):
            pairs += [{"broken": b.arguments.get("code", ""), "diagnostics": b.result.feedback(),
                       "fixed": step.arguments.get("code", "")} for b in pending]  # fmt: skip
            pending = []
        elif step.result.verdict is Verdict.ERROR:
            pending.append(step)
    return pairs


def prefix_labels(code: str, result: Result) -> list[dict[str, Any]] | None:
    """Per-line labels from the first error's location (FormL4's process-supervised verifier).

    Lines before the first error are ``good``, the rest ``bad``; all lines
    are good when the input was proved. None when the checker gives no
    location to learn from.
    """
    lines = code.splitlines()
    if result.verdict is Verdict.PROVED:
        first = len(lines) + 1
    else:
        located = error_lines(result)
        if not located:
            return None
        first = located[0]
    return [{"line": i, "text": text, "label": "good" if i < first else "bad"} for i, text in enumerate(lines, 1)]


# -- curriculum and expert iteration ------------------------------------------------------------


class Curriculum:
    """Per-problem success statistics, and selection at the right difficulty.

    The limiting resource in learning from formal feedback is a steady
    supply of problems at the right difficulty: :meth:`pick` prefers
    problems whose estimated success rate lies in ``band`` - neither solved
    every time nor hopeless (STP's "barely provable") - and fills up with
    untried ones.
    """

    def __init__(self, problems: Mapping[str, str], seed: int = 0) -> None:
        self.problems = dict(problems)
        self.attempts: dict[str, int] = {k: 0 for k in self.problems}
        self.successes: dict[str, int] = {k: 0 for k in self.problems}
        self.random = random.Random(seed)
        self._lock = threading.Lock()

    def add(self, problems: Mapping[str, str]) -> None:
        """Grow the problem set (e.g. with filtered conjectures)."""
        with self._lock:
            for k, v in problems.items():
                if k not in self.problems:
                    self.problems[k], self.attempts[k], self.successes[k] = v, 0, 0

    def record(self, problem: str, solved: bool) -> None:
        with self._lock:
            self.attempts[problem] += 1
            self.successes[problem] += int(solved)

    def rate(self, problem: str) -> float | None:
        """Empirical success rate; None if never attempted."""
        a = self.attempts[problem]
        return None if a == 0 else self.successes[problem] / a

    def solved(self) -> list[str]:
        return [k for k in self.problems if self.successes[k]]

    def pick(self, n: int, band: tuple[float, float] = (0.05, 0.7), include_solved: bool = False) -> list[str]:
        """Up to ``n`` problems: in-band first, then untried, then the rest by descending success rate.

        By default only problems without a verified solution are picked, as in
        expert iteration; ``include_solved`` also re-picks solved ones.
        """
        ids = [k for k in self.problems if include_solved or not self.successes[k]]
        self.random.shuffle(ids)
        in_band = [k for k in ids if self.rate(k) is not None and band[0] <= self.rate(k) <= band[1]]
        untried = [k for k in ids if self.rate(k) is None]
        rest = sorted((k for k in ids if k not in in_band and k not in untried), key=lambda k: -(self.rate(k) or 0))
        return (in_band + untried + rest)[:n]


@dataclass
class ExpertIteration:
    dataset: dict[str, Step] = field(default_factory=dict)  # problem id -> a verified solution
    curriculum: Curriculum | None = None
    history: list[dict[str, int]] = field(default_factory=list)  # per round: attempted, new, total, errors
    stopped: str | None = None  # why the run ended early (e.g. budget exceeded), if it did


def expert_iteration(
    problems: Mapping[str, str] | Curriculum,
    attempt: Callable[[str], Step | None],
    *,
    train: Callable[[list[Step]], None] | None = None,
    rounds: int = 3,
    per_round: int = 64,
    tries: int = 1,
    accept: Callable[[Result], bool] = lambda r: r.verdict is Verdict.PROVED,
    workers: int = 8,
) -> ExpertIteration:
    """Search, keep what the checker verifies, train on it, repeat (Polu et al.; DeepSeek-/Goedel-Prover).

    ``attempt(statement)`` tries one problem with the current model (any
    pattern: refine, sketch_and_fill, step_search, an Agent...) and returns
    a Step. Verified solutions accumulate in ``dataset``; ``train(dataset)``
    - your fine-tuning step - runs after each round, so the next round's
    attempts use the improved model. The curriculum steers each round
    toward problems at the right difficulty.
    """
    curriculum = problems if isinstance(problems, Curriculum) else Curriculum(problems)
    run = ExpertIteration(curriculum=curriculum)
    for _ in range(rounds):
        batch = [p for p in curriculum.pick(per_round) for _ in range(tries)]
        if not batch:
            break

        def go(pid: str) -> tuple[str, Step | None, str | None]:
            try:
                return pid, attempt(curriculum.problems[pid]), None
            except BudgetExceeded:
                raise
            except Exception as e:  # one failed attempt (an API hiccup...) is a miss, not the end of the run
                return pid, None, f"{type(e).__name__}: {e}"

        try:
            with ThreadPoolExecutor(workers) as pool:
                outcomes = list(pool.map(go, batch))
        except BudgetExceeded as e:
            run.stopped = str(e)
            break
        new = 0
        for pid, step, _ in outcomes:
            ok = step is not None and accept(step.result)
            curriculum.record(pid, ok)
            if ok and pid not in run.dataset:
                run.dataset[pid], new = step, new + 1
        errors = sum(1 for _, _, err in outcomes if err)
        run.history.append({"attempted": len(batch), "new": new, "total": len(run.dataset), "errors": errors})
        if train is not None and new:
            train(list(run.dataset.values()))
    return run


# -- evaluation ------------------------------------------------------------------------------


@dataclass
class Attempt:
    """One run of a pipeline on one problem, scored stage by stage."""

    problem: str  # the problem's id
    outcome: Any  # what ``solve`` returned: an Answer, a Step, a list of Steps, or None
    executable: bool  # the final formal artifact ran (any verdict but error)
    decisive: bool  # the backend reached a decisive verdict on it
    verified: bool  # the pipeline claims a verified answer
    faithful: bool | None  # the formalization means the problem (None: not judged)
    correct: bool | None  # the end answer is right (None: no judge)
    repairs: int  # backend runs before the final one
    tokens: int | None  # LLM tokens, when the outcome records them (Agent answers do)
    error: str | None = None

    @property
    def false_accept(self) -> bool:
        """Verified, yet wrong: the failure formal methods exist to prevent."""
        return self.verified and self.correct is False


@dataclass
class Report:
    """Per-stage results of :func:`evaluate`: where a pipeline fails, not just how often.

    A statement can check without meaning the right thing, and a program can
    run while solving the wrong problem, so every stage gets its own rate.
    Over ``k`` attempts per problem, ``pass@k`` counts problems solved at
    least once and ``pass^k`` problems solved every time (reliability).
    """

    attempts: list[Attempt]
    k: int

    def _rate(self, values: list[Any]) -> float | None:
        judged = [v for v in values if v is not None]
        return sum(map(bool, judged)) / len(judged) if judged else None

    def rates(self) -> dict[str, float | None]:
        a = self.attempts
        by_problem: dict[str, list[Attempt]] = {}
        for x in a:
            by_problem.setdefault(x.problem, []).append(x)
        judged = {p: xs for p, xs in by_problem.items() if all(x.correct is not None for x in xs)}
        return {
            "executable": self._rate([x.executable for x in a]),
            "decisive": self._rate([x.decisive for x in a]),
            "verified": self._rate([x.verified for x in a]),
            "faithful": self._rate([x.faithful for x in a]),
            "correct": self._rate([x.correct for x in a]),
            "false_accept": self._rate([x.false_accept if x.correct is not None else None for x in a]),
            "pass@k": self._rate([any(x.correct for x in xs) for xs in judged.values()]) if judged else None,
            "pass^k": self._rate([all(x.correct for x in xs) for xs in judged.values()]) if judged else None,
            "mean_repairs": sum(x.repairs for x in a) / len(a) if a else None,
            "mean_tokens": (sum(t) / len(t)) if (t := [x.tokens for x in a if x.tokens is not None]) else None,
            "errors": self._rate([x.error is not None for x in a]),
        }

    def summary(self, title: str = "") -> str:
        r = self.rates()
        lines = [f"{title} ({len({x.problem for x in self.attempts})} problems x k={self.k})".strip()]
        for key, value in r.items():
            shown = "-" if value is None else f"{value:.2f}" if key.startswith("mean") else f"{100 * value:.0f}%"
            lines.append(f"  {key:<13} {shown}")
        return "\n".join(lines)

    # Counts, for quick assertions.
    @property
    def total(self) -> int:
        return len(self.attempts)

    @property
    def valid(self) -> int:
        return sum(x.executable for x in self.attempts)

    @property
    def decisive(self) -> int:
        return sum(x.decisive for x in self.attempts)

    @property
    def correct(self) -> int:
        return sum(bool(x.correct) for x in self.attempts)

    @property
    def rows(self) -> list[dict[str, Any]]:
        return [{k: v for k, v in vars(x).items() if k != "outcome"} for x in self.attempts]


def _stages(outcome: Any) -> tuple[list[Step], Result | None, bool, int | None]:
    """(steps, final result, verified, tokens) for any pipeline outcome."""
    from formalkit.agent import Answer

    if isinstance(outcome, Answer):
        final = outcome.evidence[-1].result if outcome.evidence else outcome.steps[-1].result if outcome.steps else None
        return outcome.steps, final, outcome.verified, outcome.usage.get("total_tokens", 0)
    steps = [outcome] if isinstance(outcome, Step) else list(outcome or [])
    final = steps[-1].result if steps else None
    return steps, final, bool(final and final.decisive), None


def evaluate(
    problems: Mapping[str, Any],
    solve: Callable[[Any], Any],
    judge: Callable[[Any, Any], bool] | None = None,
    *,
    fidelity: Callable[[Any, Any], bool | None] | None = None,
    k: int = 1,
    workers: int = 8,
) -> Report:
    """Evaluate a pipeline by execution, stage by stage, ``k`` times per problem.

    ``solve(problem)`` runs the pipeline and returns an Answer (an Agent), a
    Step, or a list of Steps (a pattern). ``judge(problem, outcome)`` decides
    end correctness - ideally against tool-computed ground truth, since
    hand-written expected answers are themselves often wrong.
    ``fidelity(problem, outcome)`` decides whether the formalization means
    the problem (e.g. :func:`~formalkit.patterns.smt_equivalent` or
    :func:`~formalkit.patterns.lean_equivalent` against a reference), or
    returns None when it cannot tell. A crashing attempt counts as a failure
    of every stage, with its error recorded.
    """
    jobs = [(pid, problem) for pid, problem in problems.items() for _ in range(k)]

    def run(job: tuple[str, Any]) -> Attempt:
        pid, problem = job
        try:
            outcome = solve(problem)
            steps, final, verified, tokens = _stages(outcome)
            return Attempt(
                pid, outcome,
                executable=final is not None and final.verdict is not Verdict.ERROR,
                decisive=bool(final and final.decisive),
                verified=verified,
                faithful=fidelity(problem, outcome) if fidelity else None,
                correct=bool(judge(problem, outcome)) if judge else None,
                repairs=max(0, len(steps) - 1),
                tokens=tokens,
            )  # fmt: skip
        except BudgetExceeded:
            raise
        except Exception as e:
            return Attempt(pid, None, False, False, False, None, False if judge else None, 0, None,
                           f"{type(e).__name__}: {e}")  # fmt: skip

    with ThreadPoolExecutor(workers) as pool:
        attempts = list(pool.map(run, jobs))
    return Report(attempts, k)
