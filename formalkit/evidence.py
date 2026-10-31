"""Evidence policies: which tool runs back an answer, and whether they are good enough.

A policy is any callable ``policy(steps, cited) -> list[Step]``. ``steps`` are
the runs so far, ``cited`` the run numbers (1-based) the model named in its
``finish`` call, or None. It returns the runs that back the answer, or
raises :class:`Rejected` with a reason the model is shown.

    Agent(llm, backends=["z3"], evidence=nonvacuous())
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING, Callable, Optional, Sequence

from formalkit.core import Verdict

if TYPE_CHECKING:
    from formalkit.agent import Step

Policy = Callable[[Sequence["Step"], Optional[Sequence[int]]], list]


class Rejected(Exception):
    """The answer's evidence is not acceptable; the message tells the model why."""


def cited_or_last(steps: Sequence[Step], cited: Sequence[int] | None = None) -> list[Step]:
    """The default policy: the runs the model cites, or else its most recent run.

    Every backing run must be decisive. Citing several runs lets one answer
    rest on several verdicts, e.g. "3 colors suffice (sat) and 2 do not (unsat)".
    """
    if cited:
        bad = [n for n in cited if not 1 <= n <= len(steps)]
        if bad:
            raise Rejected(f"run numbers {bad} do not exist; there are runs #1..#{len(steps)}.")
        backing = [steps[n - 1] for n in dict.fromkeys(cited)]
    elif steps:
        backing = [steps[-1]]
    else:
        raise Rejected("no tool run backs this answer yet. Verify it with a tool first.")
    weak = [f"#{steps.index(s) + 1} ({s.result.verdict})" for s in backing if not s.result.decisive]
    if weak:
        raise Rejected(
            f"run {', '.join(weak)} is not decisive. Verify the answer with a tool first "
            "(e.g. assert the negation of your claim and get unsat), then call finish."
        )
    return backing


def nonvacuous(policy: Policy = cited_or_last) -> Policy:
    """Reject proofs by contradiction whose premises are already contradictory.

    An ``unsat`` from premises + negated claim proves the claim only if the
    premises alone are satisfiable; otherwise *every* claim is "proved". For
    each backing SMT-LIB ``unsat`` run, this re-runs the script without the
    negated claim - the assertion named ``goal``, or else the last one - and
    rejects the answer if that is unsat too. Confirming runs are added to the evidence,
    so ``answer.recheck()`` re-establishes them as well.
    """

    def check(steps: Sequence[Step], cited: Sequence[int] | None = None) -> list[Step]:
        from formalkit.agent import Step

        backing = policy(steps, cited)
        evidence = []
        for step in backing:
            if step.result.details.get("vacuous"):  # the backend itself found the premises contradictory
                raise Rejected(
                    f"{step.backend} reports that the premises are contradictory (vacuous proof), so the "
                    "proof would establish any claim. Fix the encoding of the premises and try again."
                )
            spec = step.ref.spec if step.ref else None
            if step.result.verdict is Verdict.UNSAT and spec and spec.language.startswith("SMT-LIB"):
                premises = drop_last_assert(step.arguments.get("code", ""))
                if premises is not None:
                    args = {**step.arguments, "code": premises}
                    result = step.ref.call(args)
                    if result.verdict is Verdict.UNSAT:
                        raise Rejected(
                            "the premises alone are unsatisfiable (your script without the negated claim is also "
                            "unsat), so the proof is vacuous: it would prove any claim. Fix the encoding of the "
                            "premises; mark the negated claim with (! ... :named goal) or put it in "
                            "(check-sat-assuming ...), and try again."
                        )
                    evidence.append(Step(step.backend, args, result, step.ref))
            evidence.append(step)
        return evidence

    return check


def drop_last_assert(script: str) -> str | None:
    """``script`` with its negated claim removed - the premises alone - or None if there is no claim.

    The claim is, in order: the assumptions of a final ``(check-sat-assuming
    ...)`` (replaced by a plain ``(check-sat)``), else the assertion named
    ``goal`` - ``(assert (! (not claim) :named goal))`` - else the last
    top-level assertion.
    """
    forms = top_level_forms(script)
    heads = [(a, b, script[a:b].lstrip("( \t\r\n")) for a, b in forms]
    checks = [(a, b, t) for a, b, t in heads if t.startswith("check-sat")]
    if checks and checks[-1][2].startswith("check-sat-assuming"):
        start, end, _ = checks[-1]
        return script[:start] + "(check-sat)" + script[end:]
    asserts = [(a, b) for a, b, t in heads if t.startswith("assert")]
    if not asserts:
        return None
    named = [(a, b) for a, b in asserts if re.search(r":named\s+\|?goal\|?\s*\)", script[a:b])]
    start, end = (named or asserts)[-1]
    return script[:start] + script[end:]


def top_level_forms(script: str) -> list[tuple[int, int]]:
    """(start, end) offsets of top-level s-expressions, skipping comments, strings and |quoted| symbols."""
    forms, depth, start, i, n = [], 0, 0, 0, len(script)
    while i < n:
        c = script[i]
        if c == ";":
            while i < n and script[i] != "\n":
                i += 1
        elif c == '"':
            i += 1
            while i < n and not (script[i] == '"' and script[i + 1 : i + 2] != '"'):
                i += 2 if script[i] == '"' else 1  # "" is an escaped quote
        elif c == "|":
            i = script.find("|", i + 1)
            if i < 0:
                break
        elif c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                forms.append((start, i + 1))
        i += 1
    return forms
