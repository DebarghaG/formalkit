"""The backend as judge of artifacts: equivalence, uniqueness, disagreement, labels.

These are the checks that turn a formal tool into a source of trustworthy
data and evaluation: are two formalizations the same (semantic accuracy,
VERGE, NL2Lean)? does a generated puzzle have exactly one solution
(PuzzleClone)? do two solvers disagree (LAST-style fuzzing)? what does a
partial program's run say about it (solver-labelled supervision)?
"""

from __future__ import annotations

import re
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from typing import Callable, Sequence

from formalkit.agent import Step
from formalkit.client import Backend
from formalkit.core import Result, Verdict
from formalkit.evidence import top_level_forms

# set-logic is left out on purpose: two formalizations may name different logics; the solver infers one.
_DECL_HEADS = ("set-option", "declare-sort", "define-sort", "declare-fun", "declare-const", "define-fun",
               "define-fun-rec", "define-funs-rec", "declare-datatypes", "declare-datatype")  # fmt: skip


def _forms(script: str) -> list[str]:
    return [script[a:b] for a, b in top_level_forms(script)]


def _head(form: str) -> str:
    match = re.match(r"\(\s*([^\s()]+)", form)
    return match.group(1) if match else ""


def _assertions(script: str) -> list[str]:
    """The script's asserted terms. Raises ValueError for anything that is not a plain, well-formed set of
    assertions - a silently dropped or misread assertion would turn into a false equivalence."""
    from formalkit.adapters._smtlib import parse_sexprs, render, unfence

    try:
        parsed = parse_sexprs(unfence(script))
    except (ValueError, IndexError):
        raise ValueError("the script's parentheses are unbalanced") from None
    if any(isinstance(f, list) and f[:1] in (["push"], ["pop"], ["reset"], ["reset-assertions"]) for f in parsed):
        raise ValueError("scripts with push/pop/reset have no single set of assertions; compare flat scripts")
    terms = []
    for form in parsed:
        if isinstance(form, list) and form[:1] == ["assert"]:
            if len(form) != 2:
                raise ValueError(f"malformed assertion {render(form)}: assert takes exactly one term")
            terms.append(render(form[1]))
    return terms


def smt_equivalent(smt: Backend, a: str, b: str, *, timeout: float = 30) -> Result:
    """Are two SMT-LIB formalizations equivalent? Their assertions are compared as wholes.

    PROVED: equivalent (no assignment satisfies one but not the other).
    REFUTED: not equivalent; ``counterexample`` is an assignment that tells
    them apart. Both scripts must use the same names for the same things;
    declarations are merged.
    """
    decls = list(dict.fromkeys(f.strip() for f in _forms(a) + _forms(b) if _head(f) in _DECL_HEADS))
    conj = lambda xs: "true" if not xs else xs[0] if len(xs) == 1 else f"(and {' '.join(xs)})"  # noqa: E731
    try:
        left, right = conj(_assertions(a)), conj(_assertions(b))
    except ValueError as e:
        return Result(Verdict.ERROR, str(e), backend=smt.name)
    script = "\n".join([*decls, f"(assert (not (= {left} {right})))", "(check-sat)", "(get-model)"])
    result = smt.run(script, timeout=timeout)
    if result.verdict is Verdict.UNSAT:
        return Result(Verdict.PROVED, "equivalent: no assignment distinguishes them", {"proof": script}, result.backend)
    if result.verdict is Verdict.SAT:
        return Result(Verdict.REFUTED, f"not equivalent; an assignment that tells them apart:\n{result.output}",
                      {"counterexample": result.model or result.output}, result.backend)  # fmt: skip
    return result


def lean_equivalent(lean: Backend, a: str, b: str, *, header: str = "import Mathlib", timeout: float = 120) -> Result:
    """Are two Lean propositions equivalent? Tries to prove ``(a) ↔ (b)`` with automation.

    PROVED is a kernel-checked equivalence; anything else means
    "not shown" (automation is incomplete), not "different".
    """
    from formalkit.patterns.prove import sketch_and_fill

    filled = sketch_and_fill(lean, f"{header}\n\nexample : ({a}) ↔ ({b}) := by\n  sorry\n", timeout=timeout)
    return filled.result


def unique(smt: Backend, script: str, *, timeout: float = 30) -> Result:
    """Does an SMT-LIB problem have exactly one solution (over its declared constants)?

    PROVED: unique. REFUTED: ``counterexample`` is a second solution. The
    first solution's verdict is returned as is when it is not sat.
    """
    # (exit) would stop the solver before the blocking query below ever runs.
    from formalkit.adapters._smtlib import parse_sexprs, unfence

    try:
        parse_sexprs(unfence(script))
    except (ValueError, IndexError):
        return Result(Verdict.ERROR, "the script's parentheses are unbalanced", backend=smt.name)
    script = re.sub(r"\(\s*exit\s*\)", "", script)  # textually: never drop anything else
    first = smt.run(script if "(get-model)" in script else script + "\n(get-model)", timeout=timeout)
    if first.verdict is not Verdict.SAT:
        return first
    # Block on the declared constants only: not functions (lambdas), not (get-value ...) terms.
    values = {k: v for k, v in (first.model or {}).items() if not v.startswith("(lambda") and not k.startswith("(")}
    # Elements of uninterpreted sorts (z3 `P!val!0`, cvc5 `(as @P_0 P)`) cannot be named in a later query
    # and have no identity beyond the model: uniqueness is judged over the concrete values only.
    abstract = sorted(k for k, v in values.items() if _ABSTRACT.search(v))
    values = {k: v for k, v in values.items() if k not in abstract}
    if not values:
        return Result(Verdict.UNKNOWN, "the solution has no concrete constant values to compare"
                      + (f" (uninterpreted: {', '.join(abstract)})" if abstract else ""), first.details, first.backend)  # fmt: skip
    block = " ".join(f"(= {_symbol(k)} {v})" for k, v in values.items())
    second = smt.run(f"{script}\n(assert (not (and {block})))\n(check-sat)\n(get-model)", timeout=timeout)
    note = f" (uninterpreted constants not compared: {', '.join(abstract)})" if abstract else ""
    extra = {"uncompared": abstract} if abstract else {}
    if second.verdict is Verdict.UNSAT:
        return Result(Verdict.PROVED, f"unique solution: {values}{note}", {"model": values, **extra}, second.backend)
    if second.verdict is Verdict.SAT:
        return Result(Verdict.REFUTED, f"not unique; another solution: {second.model}{note}",
                      {"model": values, "counterexample": second.model, **extra}, second.backend)  # fmt: skip
    return second


_ABSTRACT = re.compile(r"!val!\d+|\(as @|^@")


def _symbol(name: str) -> str:
    if name.startswith("|") and name.endswith("|"):
        return name  # already quoted, as the solver printed it
    return name if re.fullmatch(r"[A-Za-z_~!@$%^&*+=<>.?/\-][\w~!@$%^&*+=<>.?/\-]*", name) else f"|{name}|"


@dataclass
class Differential:
    results: dict[str, Result]

    @property
    def disagree(self) -> bool:
        """Two backends gave contradicting decisive verdicts - a bug in one of them (or the input is unstable)."""
        return len({r.verdict for r in self.results.values() if r.decisive}) > 1


def differential(backends: Sequence[Backend], code: str, *, timeout: float = 30) -> Differential:
    """Run one input on several backends that read the same language and compare (solver fuzzing)."""
    if not backends:
        return Differential({})
    with ThreadPoolExecutor(len(backends)) as pool:
        results = list(pool.map(lambda b: b.run(code, timeout=timeout), backends))
    return Differential({b.name: r for b, r in zip(backends, results)})


LABELS = ("promising", "wrong", "unsatisfiable", "unknown", "malformed")


def label(result: Result, check: Callable[[Result], bool] | None = None) -> str:
    """Label a (possibly partial) program by what its run says (solver-in-the-loop supervision).

    ``malformed`` (rejected), ``unsatisfiable``, ``unknown``, and for runs
    with an answer ``promising`` or - when ``check`` rejects the answer,
    e.g. it contradicts known facts - ``wrong``.
    """
    if result.verdict is Verdict.ERROR:
        return "malformed"
    if result.verdict is Verdict.UNSAT:
        return "unsatisfiable"
    if result.verdict is Verdict.UNKNOWN:
        return "unknown"
    return "wrong" if check is not None and not check(result) else "promising"


def best_of(steps: Sequence[Step], check: Callable[[Result], bool] | None = None) -> Step | None:
    """Best-of-N selection by solver label: promising, then unknown, then the rest."""
    rank = {"promising": 0, "unknown": 1, "wrong": 2, "unsatisfiable": 2, "malformed": 3}
    return min(steps, key=lambda s: rank[label(s.result, check)], default=None)
