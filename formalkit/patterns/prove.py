"""Proofs with holes, proof search, and repair: the backend as checker and search environment."""

from __future__ import annotations

import heapq
import itertools
import re
from concurrent.futures import ThreadPoolExecutor, as_completed, wait
from dataclasses import dataclass
from typing import Any, Callable, Sequence

from formalkit.agent import Step
from formalkit.client import Backend, State
from formalkit.core import Result, Verdict
from formalkit.llm import LLM, extract_code
from formalkit.observe import BudgetExceeded
from formalkit.patterns.generate import Context, layouts

AUTOMATION = {
    "lean": ["rfl", "decide", "norm_num", "simp", "omega", "linarith", "nlinarith", "positivity", "ring",
             "simp_all", "tauto", "aesop"],
    "isabelle": ["by simp", "by auto", "by arith", "by presburger", "by blast", "by fastforce", "by force",
                 "by linarith"],
}  # fmt: skip
_FENCE_BLOCKS = re.compile(r"```[^\n`]*\n(.*?)```", re.DOTALL)


def _tolerant(fn: Callable[..., Any], *args: Any) -> list:
    """``list(fn(*args))``, or [] when the call fails (e.g. a transient model API error).

    One failed proposal must not abort a whole search or sketch; a spent
    :class:`~formalkit.BudgetExceeded` still stops everything.
    """
    try:
        return list(fn(*args))
    except BudgetExceeded:
        raise
    except Exception:
        return []


def _ask(llm: LLM, prompt: str, n: int = 1, **overrides: Any) -> list[str]:
    """``llm.ask``, retried once when every reply is empty.

    Reasoning models can spend the whole token budget thinking and return no
    content; that is not an answer, and one retry usually gets one.
    """
    replies = llm.ask(prompt, n=n, **overrides)
    if not any(r.strip() for r in replies):
        replies = llm.ask(prompt, n=n, **overrides)
    return [r for r in replies if r.strip()]


def _automation(backend: Backend) -> list[str]:
    return AUTOMATION.get(backend.name.split("+")[0], [])


# -- holes ------------------------------------------------------------------------------


# Comment-only masking, kept for callers that use it (``pin``); prefer ``_mask``,
# which also handles nested comments, strings and cartouches.
_COMMENTS = re.compile(r"--[^\n]*|/-.*?-/|\(\*.*?\*\)", re.DOTALL)


_CHAR_LIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")


def _ident_char(c: str) -> bool:
    return c.isalnum() or c in "_'!?.₀₁₂₃₄₅₆₇₈₉"


def _mask(code: str) -> str:
    """``code`` with comments, string literals and Isabelle cartouches blanked (same length, newlines kept).

    Handles Lean ``--`` / nested ``/- -/`` comments, ML/Isabelle ``(* *)``
    comments, ``"..."`` strings with escapes, and nested ``\\<open>...\\<close>``.
    """
    out, i, n = list(code), 0, len(code)

    def blank(a: int, b: int) -> None:
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "

    pairs = (("/-", "-/"), ("(*", "*)"), ("\\<open>", "\\<close>"))
    while i < n:
        if code.startswith("--", i):
            j = code.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
            continue
        for opener, closer in pairs:
            if code.startswith(opener, i):
                depth, j = 1, i + len(opener)
                while j < n and depth:
                    if code.startswith(opener, j):
                        depth, j = depth + 1, j + len(opener)
                    elif code.startswith(closer, j):
                        depth, j = depth - 1, j + len(closer)
                    else:
                        j += 1
                blank(i, j)
                i = j
                break
        else:
            if code[i] == '"':
                j = i + 1
                while j < n and code[j] != '"':
                    j += 2 if code[j] == "\\" else 1
                blank(i, j + 1)
                i = j + 1
            elif code[i] == "'" and (i == 0 or not _ident_char(code[i - 1])) and _CHAR_LIT.match(code, i):
                j = _CHAR_LIT.match(code, i).end()  # a char literal such as '"' does not open a string
                blank(i, j)
                i = j
            else:
                i += 1
    return "".join(out)


def holes(code: str, marker: str = "sorry") -> list[int]:
    """Offsets of ``marker`` holes in ``code``, ignoring comments, strings and cartouches."""
    masked = _mask(code)
    return [m.start() for m in re.finditer(rf"(?<![\w.']){re.escape(marker)}(?![\w'])", masked)]


# A hole right after one of these is a term, not a tactic: fill it with `by <tactic>`.
_TERM_POSITION = re.compile(r"(:=|\(|,|⟨|\bexact|\bfrom|\brefine|\buse|\bshow\s.*\bfrom)\s*$")


def _fill(code: str, at: int, marker: str, text: str) -> str:
    """Put ``text`` where the hole at ``at`` is, keeping multi-line text indented under it.

    In term position (``:= sorry``, ``⟨h, sorry⟩``, ``exact sorry``) a tactic
    proof is wrapped as ``by ...``; text that already starts with ``by`` is
    used as is (also Isabelle's ``by simp``).
    """
    line_start = code.rfind("\n", 0, at) + 1
    column = at - line_start
    text = text.strip()
    term = _TERM_POSITION.search(_mask(code[line_start:at])) and not re.match(r"by\b", text)
    if term and "\n" in text:
        pad = " " * (column + 2)
        return code[:at] + "(by\n" + pad + text.replace("\n", "\n" + pad) + ")" + code[at + len(marker) :]
    if term:
        text = f"(by {text})"
    return code[:at] + text.replace("\n", "\n" + " " * column) + code[at + len(marker) :]


def _attempts(code: str, at: int, marker: str, candidates: Sequence[str]) -> list[tuple[str, str]]:
    """``(candidate, filled file)`` for every candidate and each of its plausible layouts.

    Models write multi-line fills either relative to the hole or at the
    file's indentation; both readings are tried and the backend decides.
    """
    column = at - (code.rfind("\n", 0, at) + 1)
    after_by = re.search(r"(?<![\w.])by\s*$", _mask(code[:at])) is not None
    out, seen = [], set()
    for candidate in candidates:
        texts = [candidate]
        if after_by and re.match(r"\s*by\b", candidate):  # `by` twice: also try it once
            texts.append(re.sub(r"^\s*by\b[ \t]*\n?", "", candidate, count=1))
        for text in (t for c in texts for t in layouts(c, column)):
            filled = _fill(code, at, marker, text)
            if filled not in seen:
                seen.add(filled)
                out.append((candidate, filled))
    return out


_DISGUISED = re.compile(r"(?<![\w.'])(admit|oops|sorry)(?![\w'])")


def _in_context(code: str, at: int, marker: str) -> str:
    """When the backend reports no goal for a hole: the file, with that hole marked."""
    return f"(the hole marked ⟪HOLE⟫ in)\n{code[:at]}⟪HOLE⟫{code[at + len(marker):]}"


def _first(items: Sequence[Any], run: Callable[[Any], Result], good: Callable[[Result], bool],
           workers: int = 8, grace: float = 2.0) -> Any:  # fmt: skip
    """The best-ranked item (earliest in ``items``) whose result is ``good``, or None - without
    waiting for slow stragglers.

    Once some item succeeds, higher-ranked items still running get ``grace``
    seconds to finish; then the best-ranked success wins. A single slow
    candidate (an ``aesop`` grinding to the timeout) therefore cannot hold up
    a fill that ``simp`` already found. Runs still in flight finish in the background.
    """
    if not items:
        return None
    pool = ThreadPoolExecutor(min(workers, len(items)))
    futures = [pool.submit(run, item) for item in items]
    try:
        for future in as_completed(futures):
            if not good(future.result()):
                continue
            k = futures.index(future)
            wait(futures[:k], timeout=grace)
            for j, f in enumerate(futures[: k + 1]):
                if f.done() and not f.cancelled() and f.exception() is None and good(f.result()):
                    return items[j]
        return None
    finally:
        pool.shutdown(wait=False, cancel_futures=True)


def _checks(result: Result) -> bool:
    """The file checks, apart from holes still open: proved, or unknown only because of holes."""
    return result.verdict is Verdict.PROVED or (result.verdict is Verdict.UNKNOWN and not result.details.get("timeout"))


@dataclass
class Filled:
    """The outcome of :func:`sketch_and_fill` and :func:`decompose`."""

    code: str  # the sketch with every closable hole filled
    result: Result  # the backend's verdict on ``code``
    fills: list[str | None]  # what closed each hole, None where nothing did

    @property
    def proved(self) -> bool:
        return self.result.verdict is Verdict.PROVED


def sketch_and_fill(
    backend: Backend,
    sketch: str,
    *,
    closers: Sequence[str] | None = None,
    close: Callable[[str], Sequence[str]] | None = None,
    marker: str = "sorry",
    timeout: float = 120,
) -> Filled:
    """Close the holes of a proof sketch (Draft, Sketch, and Prove).

    Each ``marker`` hole is tried, in order, with the ``closers`` (default:
    the backend's automation from :data:`AUTOMATION`) and then with whatever
    ``close(goal)`` proposes - e.g. :func:`llm_close`, a model asked for
    proofs of that subgoal. A candidate is accepted when the file still
    checks with the other holes open; the backend is the only judge.
    Candidates for one hole run in parallel.
    """
    closers = list(_automation(backend) if closers is None else closers)
    first = backend.run(sketch, timeout=timeout)
    if first.verdict is Verdict.ERROR or not holes(sketch, marker):
        return Filled(sketch, first, [])
    goals, n = first.goals, len(holes(sketch, marker))
    code, fills = sketch, []
    for i in range(n):
        at = holes(code, marker)[fills.count(None)]  # filled holes are gone; skipped ones remain
        goal = goals[i] if len(goals) == n else _in_context(code, at, marker)
        # A fill must not smuggle in another hole, plain or disguised (`admit`, `oops`).
        proposed = _tolerant(close, goal) if close else []
        candidates = [
            c for c in dict.fromkeys([*closers, *proposed]) if not holes(c, marker) and not _DISGUISED.search(_mask(c))
        ]
        attempts = _attempts(code, at, marker, candidates)
        last = len(holes(code, marker)) == 1  # nothing else is open: only a proof will do
        ok = _first(attempts, lambda a: backend.run(a[1], timeout=timeout),
                    lambda r, last=last: r.verdict is Verdict.PROVED if last else _checks(r))  # fmt: skip
        fills.append(None if ok is None else ok[0])
        if ok is not None:
            code = ok[1]
    if code == sketch:
        return Filled(code, first, fills)
    # The final file is certified against the sketch itself: its statements are the challenge.
    challenge = {"challenge": sketch} if "challenge" in backend.spec.inputs and not holes(code, marker) else {}
    return Filled(code, backend.run(code, timeout=timeout, **challenge), fills)


def llm_close(llm: LLM, language: str = "Lean 4", n: int = 3, *, context: Context | None = None,
              **overrides: Any) -> Callable[[str], list[str]]:  # fmt: skip
    """A ``close`` for :func:`sketch_and_fill`: ask the model for ``n`` candidate proofs of one subgoal."""

    def close(goal: str) -> list[str]:
        extra = context(goal) if context else ""
        prompt = (
            f"Prove this {language} goal. Reply with {n} alternative proofs, each being exactly the text that "
            "replaces `sorry` - no theorem statement - in separate fenced code blocks (in Lean: the tactics; "
            "in Isabelle: a proof method such as `by auto`, or an apply-script ending in `done`).\n\n"
            f"Goal:\n{goal}" + (f"\n\n{extra}" if extra else "")
        )
        text = (_ask(llm, prompt, **overrides) or [""])[0]
        blocks = [b.strip() for b in _FENCE_BLOCKS.findall(text) if b.strip()]
        return (blocks or [extract_code(text)] if text.strip() else [])[:n]  # no fences: the reply is the proof

    return close


def decompose(
    llm: LLM,
    backend: Backend,
    code: str,
    *,
    depth: int = 2,
    width: int = 2,
    context: Context | None = None,
    timeout: float = 120,
) -> Filled:
    """Recursive decomposition (POETRY, DeepSeek-Prover-V2, Delta Prover).

    Fill what automation and the model can close directly; for each hole
    that stays open, have the model write a *sketch* of that subproof -
    intermediate ``have`` steps whose proofs are again ``sorry`` - and
    recurse into the new holes, up to ``depth`` levels and ``width``
    sketches per hole. Every intermediate file is checked by the backend,
    and the final verdict is the backend's on the complete file.
    """
    language = backend.spec.language
    filled = sketch_and_fill(backend, code, close=llm_close(llm, language, context=context), timeout=timeout)
    if filled.proved or depth <= 0 or filled.result.verdict is Verdict.ERROR:
        return filled
    current = filled.code
    goals = filled.result.goals
    open_holes = holes(current)
    for j, at in enumerate(open_holes):
        goal = goals[j] if len(goals) == len(open_holes) else _in_context(current, at, "sorry")
        extra = context(goal) if context else ""
        replies = _tolerant(
            lambda prompt: _ask(llm, prompt, n=width, temperature=0.8),
            f"This {language} goal is too hard to prove in one step:\n\n{goal}\n\n"
            "Write a proof SKETCH for it: a few intermediate claims and the final steps that use them, leaving "
            "every intermediate proof as `sorry` (in Lean: `have h : P := by sorry`; in Isabelle: "
            "`have \"P\" sorry`). It replaces one `sorry`, so give only that replacement text - no theorem "
            "statement - in a fenced code block."
            + (f"\n\n{extra}" if extra else ""),
        )
        sketches = [x for x in dict.fromkeys(extract_code(r) for r in replies) if x.strip()]
        for _, candidate in _attempts(current, at, "sorry", sketches):
            if _checks(backend.run(candidate, timeout=timeout)):
                deeper = decompose(llm, backend, candidate, depth=depth - 1, width=width, context=context,
                                   timeout=timeout)  # fmt: skip
                if deeper.proved:
                    return deeper
    return filled


# -- repair ---------------------------------------------------------------------------------

Fixer = Callable[[str, Result], Sequence[str]]  # (code, failed result) -> candidate repaired programs


def error_lines(result: Result) -> list[int]:
    """1-based lines of the backend's error messages, when it reports them."""
    return sorted({m["line"] for m in result.details.get("messages", [])
                   if m.get("severity") == "error" and isinstance(m.get("line"), int)})  # fmt: skip


def localize(code: str, result: Result, radius: int = 2) -> str:
    """The failing lines with a little context, numbered, followed by the feedback."""
    lines, marks = code.splitlines(), set(error_lines(result))
    if not marks:
        return result.feedback()
    keep = sorted({k for m in marks for k in range(max(1, m - radius), min(len(lines), m + radius) + 1)})
    shown, last = [], 0
    for k in keep:
        if last and k != last + 1:
            shown.append("     ...")
        shown.append(f"{'>>' if k in marks else '  '}{k:4} | {lines[k - 1]}")
        last = k
    return "\n".join(shown) + "\n\n" + result.feedback()


def tactic_swap(alternatives: Sequence[str]) -> Fixer:
    """Lyra-style tool correction: replace the failing tactic line with each alternative."""

    def fix(code: str, result: Result) -> list[str]:
        lines, out = code.splitlines(), []
        for n in error_lines(result)[:1]:
            line = lines[n - 1]
            inline = re.search(r"(:=\s*by\s+|\bby\s+)(\S.*)$", line)
            indent = line[: len(line) - len(line.lstrip())]
            for alt in alternatives:
                if inline and re.match(r"by\b", alt.strip()):  # Isabelle-style `by method`: replace from the `by`
                    new = line[: line.index("by", inline.start(1))] + alt.strip()
                elif inline:
                    new = line[: inline.start(2)] + alt
                else:
                    new = indent + alt
                out.append("\n".join([*lines[: n - 1], new, *lines[n:]]))
        return out

    return fix


def repair(
    backend: Backend,
    code: str,
    result: Result | None = None,
    *,
    fixers: Sequence[Fixer] = (),
    llm: LLM | None = None,
    rounds: int = 3,
    done: Callable[[Result], bool] = lambda r: r.verdict is Verdict.PROVED,
    context: Context | None = None,
    timeout: float = 120,
) -> list[Step]:
    """Proposal - check - repair (Baldur, PALM, Lyra, CoqPilot).

    Each round first tries the cheap symbolic ``fixers`` (in parallel), then
    asks ``llm`` with the error *localized* to the failing lines. Returns
    every attempt; the last one is the outcome.
    """
    result = result or backend.run(code, timeout=timeout)
    steps = [Step(backend.name, {"code": code}, result, backend)]
    for _ in range(rounds):
        if done(result):
            break
        candidates = list(dict.fromkeys(c for f in fixers for c in f(code, result) if c != code))
        with ThreadPoolExecutor(min(8, len(candidates) or 1)) as pool:
            tried = list(zip(candidates, pool.map(lambda c: backend.run(c, timeout=timeout), candidates)))
        fixed = next(((c, r) for c, r in tried if done(r)), None)
        if fixed:
            code, result = fixed
        elif llm is not None:
            extra = context(code) if context else ""
            reply = _tolerant(lambda prompt: _ask(llm, prompt),
                f"This {backend.spec.language} input fails:\n\n```\n{code}\n```\n\nWhere and why:\n"
                f"{localize(code, result)}" + (f"\n\n{extra}" if extra else "")
                + "\n\nFix it. Reply with the complete corrected input in a single fenced code block."
            )  # fmt: skip
            if not reply:
                break  # the model call failed: keep the attempts so far
            code = extract_code(reply[0])
            result = backend.run(code, timeout=timeout)
        else:
            break
        steps.append(Step(backend.name, {"code": code}, result, backend))
    return steps


# -- step-level search -----------------------------------------------------------------------


@dataclass
class Search:
    """The outcome of :func:`step_search`."""

    solved: State | None  # the solved state (its .proof is the checked proof), or None
    expanded: int  # states expanded
    tried: int  # steps tried

    @property
    def proof(self) -> Any:
        return self.solved.proof if self.solved else None


def step_search(
    root: State,
    propose: Callable[[State], Sequence[str]],
    *,
    budget: int = 50,
    max_depth: int = 30,
    value: Callable[[State], float] | None = None,
    timeout: float = 60,
) -> Search:
    """Best-first search over session states (GPT-f, HTPS, BFS-Prover).

    ``propose(state)`` suggests next steps, best first (e.g. :func:`llm_steps`,
    or several proposers via :func:`mix`); the backend checks each one.
    States are ranked by ``value`` (a critic or progress estimate, higher is
    better) or, by default, by fewest open goals then shallowest depth.
    Duplicate goal sets are expanded once. Stops at the first solved state
    or after ``budget`` expansions (combine with a ``Budget`` observer to
    cap calls, tokens or time).
    """
    if root.failed or root.id is None:
        return Search(root if root.solved else None, 0, 0)

    def priority(state: State) -> tuple:
        return (-value(state),) if value else (len(state.goals), len(state.path))

    tie = itertools.count()
    frontier = [(priority(root), next(tie), root)]
    seen = {tuple(root.goals)}
    expanded = tried = 0
    while frontier and expanded < budget:
        _, _, state = heapq.heappop(frontier)
        expanded += 1
        if len(state.path) >= max_depth:
            continue
        steps = list(dict.fromkeys(s.strip() for s in _tolerant(propose, state) if s and s.strip()))
        with ThreadPoolExecutor(min(8, len(steps) or 1)) as pool:
            children = list(pool.map(lambda s, st=state: st.apply(s, timeout=timeout), steps))
        tried += len(steps)
        for child in children:
            if child.solved:
                return Search(child, expanded, tried)
            if child.failed or child.id is None or tuple(child.goals) in seen:
                continue
            seen.add(tuple(child.goals))
            heapq.heappush(frontier, (priority(child), next(tie), child))
    return Search(None, expanded, tried)


def llm_steps(llm: LLM, n: int = 4, *, context: Context | None = None, **overrides: Any) -> Callable[[State], list[str]]:
    """A ``propose`` for :func:`step_search` that asks the model for ``n`` next steps.

    ``context`` adds state-dependent retrieval (REAL-Prover, Rango), e.g.
    ``Library.context()`` or a premise selector.
    """

    def propose(state: State) -> list[str]:
        spec = state.backend.spec
        goals = "\n".join(state.goals)
        extra = context(goals) if context else ""
        prompt = (
            f"You are proving a theorem in {spec.language}, one step at a time.\n\n"
            f"Current goals:\n{goals}\n\nSteps so far:\n{chr(10).join(state.path) or '(none yet)'}\n\n"
            + (f"{extra}\n\n" if extra else "")
            + f"Propose up to {n} different candidate next steps (tactics), best first, one per line, "
            "in a single fenced code block. Each line must be a complete step on its own."
        )
        text = (_ask(llm, prompt, **overrides) or [""])[0]
        steps = (_clean_step(line) for line in extract_code(text).splitlines())
        return list(dict.fromkeys(s for s in steps if s))[:n]

    return propose


_LIST_MARKER = re.compile(r"^\s*(?:\d+[.)]|[-*•])\s+")


def _clean_step(line: str) -> str:
    """One proposed step without list numbering, bullets-as-list-markers or wrapping backticks."""
    step = _LIST_MARKER.sub("", line).strip()
    if len(step) > 1 and step.startswith("`") and step.endswith("`"):
        step = step.strip("`").strip()
    return step


def mix(*proposers: Callable[[State], Sequence[str]]) -> Callable[[State], list[str]]:
    """Interleave several proposers - e.g. automation plus a model - for diverse search (MPS-Prover)."""

    def propose(state: State) -> list[str]:
        lists = [_tolerant(p, state) for p in proposers]  # one failing proposer does not silence the others
        merged = [s for group in itertools.zip_longest(*lists) for s in group if s]
        return list(dict.fromkeys(merged))

    return propose


def automation(backend: Backend) -> Callable[[State], list[str]]:
    """A proposer that always suggests the backend's automation tactics."""
    tactics = _automation(backend)
    return lambda state: list(tactics)


def suggest(state: State, propose: Callable[[State], Sequence[str]], timeout: float = 60) -> list[State]:
    """Checked suggestions for one proof state, solved ones first (LLMSTEP, Lean Copilot)."""
    steps = list(dict.fromkeys(_tolerant(propose, state)))
    with ThreadPoolExecutor(min(8, len(steps) or 1)) as pool:
        children = list(pool.map(lambda s: state.apply(s, timeout=timeout), steps))
    return sorted((c for c in children if not c.failed), key=lambda c: (not c.solved, len(c.goals)))


def probe(state: State, tactics: Sequence[str] | None = None, timeout: float = 60) -> dict[str, str]:
    """Which automation succeeds at this state: ``{tactic: "solved" | "progress" | "error"}`` (Lean4trace)."""
    tactics = list(_automation(state.backend) if tactics is None else tactics)
    with ThreadPoolExecutor(min(8, len(tactics) or 1)) as pool:
        children = list(pool.map(lambda t: state.apply(t, timeout=timeout), tactics))
    return {t: "solved" if c.solved else "error" if c.failed else "progress" for t, c in zip(tactics, children)}
