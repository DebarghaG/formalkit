"""The model writes whole formal artifacts: translate, refine, formalize, sample, route."""

from __future__ import annotations

import json
import re
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, replace
from typing import Any, Callable, Sequence

from formalkit.agent import Step
from formalkit.client import Backend
from formalkit.core import Result, Spec, Verdict
from formalkit.llm import LLM, extract_code
from formalkit.observe import BudgetExceeded

Context = Callable[[str], str]  # problem or goal -> extra prompt text (e.g. Library.context())


def refine(
    llm: LLM,
    backend: Backend,
    problem: str,
    *,
    rounds: int = 3,
    done: Callable[[Result], bool] = lambda r: r.decisive,
    instructions: str = "",
    context: Context | None = None,
    corrector: LLM | None = None,
    template: str | None = None,
    timeout: float = 60,
    **overrides: Any,
) -> list[Step]:
    """Have the model write a complete program; regenerate it from the tool's
    feedback until ``done(result)`` or ``rounds`` run out.

    With a ``template`` - a fixed formal statement with one ``sorry`` hole -
    the model writes only what goes in the hole (see :func:`pin`), so it
    cannot prove a different, easier statement than the one asked.

    One round is translator-solver separation (LINC, SATLM); more rounds add
    solver-driven self-refinement (Logic-LM, Baldur's repair). ``corrector``
    hands the repairs to a second model (MA-LoT's prover/corrector split);
    ``context`` adds retrieved material (e.g. ``Library.context()``).
    Returns every attempt; the last one is the outcome. ``overrides`` (e.g.
    ``temperature``) go to every LLM call.
    """
    spec = backend.spec
    fill = pin(template) if template else None
    extra = context(problem) if context else ""
    messages = [
        {"role": "system", "content": f"You write {spec.language} for {spec.name}.\n\n{spec.describe()}"},
        {"role": "user", "content": "\n\n".join(x for x in (problem, extra, instructions) if x) + _ask(spec, template)},
    ]  # fmt: skip
    steps: list[Step] = []
    for attempt in range(rounds):
        model = corrector if (corrector and attempt) else llm
        reply = model.chat(messages, **dict(overrides))
        text, inputs = reply_inputs(reply["content"], spec) if not fill else (extract_code(reply["content"]), {})
        for code in fill.variants(text) if fill else [text]:  # ambiguous indentation: the checker decides
            result = backend.run(code, timeout=timeout, **inputs, **(challenge_input(backend, template) if fill else {}))
            if result.verdict is not Verdict.ERROR:
                break
        steps.append(Step(backend.name, {"code": code, **inputs, **({"fill": text} if fill else {})}, result, backend))
        if done(result):
            break
        what = ("corrected replacement for `sorry` only" if fill else
                "complete corrected JSON object" if spec.inputs else "complete corrected input")
        messages += [
            reply,
            {"role": "user", "content": f"The tool returned:\n{result.feedback()}\n\nFix the problem and reply with the "
                                        f"{what} in a single fenced code block."},
        ]  # fmt: skip
    return steps


def _ask(spec: Spec, template: str | None) -> str:
    language = spec.language
    if template is None and spec.inputs:
        fields = "\n".join(f'- "{k}": {d}' + (" (optional)" if k in spec.optional else "") for k, d in spec.inputs.items())
        return (
            f"\n\nThis tool takes several inputs. Reply with ONE JSON object in a single ```json block, with "
            f'"code" (the {language} input) and:\n{fields}'
        )
    if template is None:
        return f"\n\nReply with the complete {language} input in a single fenced code block."
    return (
        f"\n\nThe statement is fixed:\n```\n{template}\n```\nReply with ONLY the text that replaces `sorry` "
        "(the proof, without restating the theorem), in a single fenced code block."
    )


def challenge_input(backend: Backend, statement: str) -> dict[str, str]:
    """``{"challenge": statement}`` for backends that certify against a fixed statement (Lean's
    ``lake comparator``), else nothing: the statement then pins only what the model may write."""
    return {"challenge": statement} if "challenge" in backend.spec.inputs else {}


def reply_inputs(content: str, spec: Spec) -> tuple[str, dict[str, str]]:
    """``(code, inputs)`` from a model reply. Backends with extra inputs are asked for a
    JSON object (see ``_ask``); anything else - or a reply that isn't valid JSON - is the code."""
    text = extract_code(content)
    if not spec.inputs:
        return text, {}
    try:
        obj = json.loads(text)
    except ValueError:
        return text, {}
    if not isinstance(obj, dict) or not isinstance(obj.get("code"), str):
        return text, {}
    inputs = {k: str(v) for k, v in obj.items() if k in spec.inputs and v not in (None, "")}
    return obj["code"], inputs


def layouts(text: str, column: int) -> list[str]:
    """The plausible readings of a model's multi-line text for a hole at ``column``.

    Models write the text that replaces a hole either relative to the hole
    or at the file's indentation (continuation lines already indented by
    ``column``). The text alone is ambiguous in indentation-sensitive
    languages, so return both readings - the more likely first - and let
    the checker decide.
    """
    lines = text.strip("\n").split("\n")
    first, rest = lines[0].strip(), lines[1:]
    as_is = "\n".join([first, *rest])
    indents = [len(line) - len(line.lstrip()) for line in rest if line.strip()]
    if column <= 0 or not indents or min(indents) < column:
        return [as_is]
    dedented = "\n".join([first, *(line[column:] if line.strip() else line for line in rest)])
    return [dedented, as_is]


class Pinned:
    """Fills the single hole of a fixed template; see :func:`pin`."""

    def __init__(self, template: str, hole: str = "sorry") -> None:
        from formalkit.patterns.prove import _mask, holes

        spots = holes(template, hole)
        if len(spots) != 1:
            raise ValueError(f"a template needs exactly one `{hole}` hole, found {len(spots)}")
        self.template, self.hole, self.at = template, hole, spots[0]
        self.column = self.at - (template.rfind("\n", 0, self.at) + 1)
        masked = _mask(template)[: self.at]  # comments, strings, cartouches and char literals blanked
        self.after_by = re.search(r"\bby\s*$", masked) is not None

    def variants(self, text: str) -> list[str]:
        """Every plausible filled file, most likely first (see :func:`layouts`)."""
        from formalkit.patterns.prove import _fill

        text = text.strip("\n")
        if self.after_by and re.match(r"\s*by\b", text):
            text = re.sub(r"^\s*by\b[ \t]*\n?", "", text, count=1)
        return list(dict.fromkeys(_fill(self.template, self.at, self.hole, t) for t in layouts(text, self.column)))

    def __call__(self, text: str) -> str:
        return self.variants(text)[0]


class PinnedBackend(Backend):
    """A backend that only accepts the text for one fixed statement's hole; see :func:`pinned`."""

    def __init__(self, inner: Backend, template: str, name: str | None = None) -> None:
        self.inner, self.fill = inner, Pinned(template)
        self.name = name or f"{inner.name}_pinned"
        spec = inner.spec
        self._spec = replace(
            spec,
            name=self.name,
            language=f"the proof that replaces `sorry` in a fixed {spec.language} statement",
            emits="only the text that fills the statement's hole (e.g. a tactic proof); the statement cannot change.",
            guidance=f"The statement is fixed:\n{template.strip()}\n\nSend ONLY the replacement for `sorry` "
                     f"(no theorem header, no imports).\n\n{spec.guidance}",
            example="",
            inputs={},
            optional=[],
            sessions=False,
        )  # fmt: skip

    @property
    def spec(self) -> Spec:
        return self._spec

    def run(self, code: str, timeout: float = 30, **inputs: str) -> Result:
        result = Result(Verdict.ERROR, "nothing to run")
        for filled in self.fill.variants(code):  # ambiguous indentation: the checker decides
            result = self.inner.run(filled, timeout, **challenge_input(self.inner, self.fill.template))
            if result.verdict is not Verdict.ERROR:
                break
        result.details["filled"] = filled
        result.backend = self.name
        return result


def pinned(backend: Backend, template: str, *, name: str | None = None) -> PinnedBackend:
    """``backend``, restricted to filling the single ``sorry`` of ``template``.

    Use it wherever a model must prove a *given* statement - an Agent, MCP,
    any pattern: the model's input can only become the hole's content, so a
    ``proved`` verdict is always about the statement that was asked.
    """
    return PinnedBackend(backend, template, name)


def pin(template: str, hole: str = "sorry") -> Pinned:
    """A function putting a model's text into the single ``hole`` of a fixed ``template``.

    This pins the statement: whatever the model writes can only fill the
    hole, so the checker's verdict is about the statement that was asked -
    not one the model quietly changed or replaced. A leading ``by`` is
    dropped when the template already has one before the hole;
    ``.variants(text)`` lists every plausible indentation of the text.
    """
    return Pinned(template, hole)


def translate_and_solve(llm: LLM, backend: Backend, problem: str, **kwargs: Any) -> Step:
    """Translate once, solve once: the model formalizes, the solver reasons."""
    return refine(llm, backend, problem, rounds=1, **kwargs)[0]


def formalize(llm: LLM, backend: Backend, statement: str, *, rounds: int = 3, hole: str = "sorry", **kwargs: Any) -> Step:
    """Turn an informal statement into a formal one, with its proof left as ``hole``.

    Succeeds when the backend accepts the statement (any verdict but error),
    so the result can go straight into a prover pattern.
    """
    instructions = (
        f"Formalize the statement only: state it as a theorem and leave the proof as `{hole}`. "
        "Do not try to prove it. Faithfulness to the informal statement matters more than anything else."
    )
    return refine(llm, backend, statement, rounds=rounds, instructions=instructions,
                  done=lambda r: r.verdict is not Verdict.ERROR, **kwargs)[-1]  # fmt: skip


def sample(llm: LLM, backend: Backend, problem: str, n: int = 5, *, temperature: float = 0.8, **kwargs: Any) -> list[Step]:
    """``n`` independent formalizations of one problem, each run through ``backend``."""
    def one() -> Step:
        try:
            return refine(llm, backend, problem, temperature=temperature, **kwargs)[-1]
        except BudgetExceeded:
            raise
        except Exception as e:  # one failed sample is an error candidate, not the end of the vote
            return Step(backend.name, {"code": ""}, Result(Verdict.ERROR, f"sample failed: {type(e).__name__}: {e}"), backend)

    with ThreadPoolExecutor(min(n, 8)) as pool:
        return list(pool.map(lambda _: one(), range(n)))


@dataclass
class Vote:
    """The outcome of :func:`vote`."""

    winner: Any  # the winning key, or None on a tie / no decisive candidates
    support: list[Step]  # the candidates that agree with the winner
    counts: dict[Any, int]


def vote(steps: Sequence[Step], key: Callable[[Step], Any] = lambda s: s.result.verdict) -> Vote:
    """Majority over decisive candidates, e.g. several independent formalizations.

    ``key`` maps a candidate to what it says (default: its verdict). Ties
    and the absence of decisive candidates give ``winner=None``.
    """
    decisive = [s for s in steps if s.result.decisive]
    counts = Counter(key(s) for s in decisive)
    ranked = counts.most_common()
    if not ranked or (len(ranked) > 1 and ranked[0][1] == ranked[1][1]):
        return Vote(None, [], dict(counts))
    winner = ranked[0][0]
    return Vote(winner, [s for s in decisive if key(s) == winner], dict(counts))


def route(chooser: LLM | Callable[[str, Sequence[Backend]], Backend], problem: str, backends: Sequence[Backend]) -> Backend:
    """Pick the formalism and solver for a problem (adaptive formalism selection).

    ``chooser`` is a model, asked to choose among the backends' specs, or any
    function ``(problem, backends) -> backend`` such as a trained classifier.
    """
    if not isinstance(chooser, LLM):
        return chooser(problem, backends)
    menu = "\n".join(f"- {b.name}: {b.spec.language}; decides {b.spec.authority} Good for: {b.spec.use}" for b in backends)
    reply = chooser.ask(
        f"Which formal tool is the best fit for this problem?\n\nProblem:\n{problem}\n\nTools:\n{menu}\n\n"
        "Answer with the tool name only."
    )[0]
    names = {b.name: b for b in backends}
    for token in re.findall(r"[\w+-]+", reply):
        if token in names:
            return names[token]
    return backends[0]


def backtranslate(llm: LLM, formal: str, language: str = "Lean 4", **overrides: Any) -> str:
    """Formal -> informal: a faithful natural-language rendering (distilled backtranslation)."""
    return llm.ask(
        f"State in precise natural language exactly what this {language} statement says. Do not prove it, "
        f"do not add or drop hypotheses. Reply with the statement only.\n\n{formal}",
        **overrides,
    )[0].strip()


def cycle_consistency(llm: LLM, informal: str, formal: str, *, language: str = "Lean 4", judge: LLM | None = None) -> float:
    """How well meaning survives informal -> formal -> informal, from 0 to 1.

    Backtranslates ``formal`` and asks ``judge`` (default ``llm``) whether it
    says the same as ``informal``; usable as a reward for autoformalization.
    """
    back = backtranslate(llm, formal, language)
    verdict = (judge or llm).ask(
        "Do these two statements say exactly the same thing mathematically (same hypotheses, same conclusion, "
        f"same quantifiers)? Answer with a number from 0 (unrelated) to 10 (identical in meaning) only.\n\n"
        f"A: {informal}\n\nB: {back}"
    )[0]
    match = re.search(r"\d+(\.\d+)?", verdict)
    return min(10.0, float(match.group())) / 10 if match else 0.0


@dataclass
class Conjecture:
    code: str
    result: Result  # the backend's verdict on the statement (with its hole open)
    trivial: bool  # closed by automation alone
    valid: bool  # elaborates


def conjecture(
    llm: LLM,
    backend: Backend,
    seed: str,
    n: int = 5,
    *,
    hole: str = "sorry",
    trivial: Callable[[str], bool] | None = None,
    timeout: float = 120,
) -> list[Conjecture]:
    """Propose new statements near ``seed`` and filter them (LeanConjecturer, STP).

    Each conjecture must elaborate (``valid``); ``trivial`` marks those that
    automation already proves - by default via
    :func:`~formalkit.patterns.prove.sketch_and_fill` with the backend's
    automation. Keep ``valid and not trivial`` ones as new problems.
    """
    from formalkit.patterns.prove import sketch_and_fill

    if trivial is None:
        def trivial(code: str) -> bool:
            return sketch_and_fill(backend, code, timeout=timeout).proved

    replies = llm.ask(
        f"Here is some {backend.spec.language}:\n\n{seed}\n\nState ONE new, non-trivial, plausibly true theorem "
        f"related to it, with the proof left as `{hole}`. Reply with a complete file in a single fenced code block.",
        n=n, temperature=1.0,
    )  # fmt: skip
    out = []
    for code in dict.fromkeys(extract_code(r) for r in replies):
        result = backend.run(code, timeout=timeout)
        valid = result.verdict is not Verdict.ERROR
        out.append(Conjecture(code, result, valid and trivial(code), valid))
    return out


@dataclass
class Consensus:
    """The outcome of :func:`consensus`."""

    answer: Any  # the agreed answer, or None when abstaining
    confidence: float  # share of all attempts that back the answer
    abstained: bool
    attempts: list[Any]  # every independent outcome
    counts: dict[Any, int]


def _verified_answer(outcome: Any) -> Any:
    """The default consensus key: a verified Answer's normalized text, a decisive Step's verdict."""
    from formalkit.agent import Answer

    if isinstance(outcome, Answer):
        return " ".join(outcome.answer.lower().split()) if outcome.verified and outcome.answer else None
    if isinstance(outcome, Step):
        return outcome.result.verdict if outcome.result.decisive else None
    return None


def consensus(
    solve: Callable[[], Any],
    n: int = 5,
    *,
    key: Callable[[Any], Any] = _verified_answer,
    threshold: float = 0.6,
    workers: int = 5,
) -> Consensus:
    """Answer only when independent attempts agree; otherwise abstain (selective verification).

    Runs ``solve()`` ``n`` times (an Agent, a pattern...). ``key`` maps an
    outcome to its answer, or None when it has no trustworthy one (by
    default: unverified answers do not vote). The answer is the most common
    key; its confidence is its share of *all* attempts, so failed and
    unverified attempts count against it. Below ``threshold``, abstain.
    """

    def one() -> Any:
        try:
            return solve()
        except BudgetExceeded:
            raise
        except Exception:
            return None

    with ThreadPoolExecutor(min(n, workers)) as pool:
        outcomes = list(pool.map(lambda _: one(), range(n)))
    counts = Counter(k for k in (key(o) for o in outcomes if o is not None) if k is not None)
    if not counts:
        return Consensus(None, 0.0, True, outcomes, {})
    answer, votes = counts.most_common(1)[0]
    confidence = votes / n
    tied = sum(1 for v in counts.values() if v == votes) > 1
    abstain = confidence < threshold or tied
    return Consensus(None if abstain else answer, confidence, abstain, outcomes, dict(counts))
