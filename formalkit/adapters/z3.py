from __future__ import annotations

import re

from formalkit.adapters._smtlib import classify, hint, unfence
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir


# z3 prints echoed strings bare, so (echo "unsat") would read as a verdict: tag such echoes.
_ECHO_VERDICT = re.compile(r'\(\s*echo\s+"\s*(sat|unsat|unknown)\s*"\s*\)')


_OPTIMIZES = re.compile(r"\(\s*(maximize|minimize)\b")


class Z3(Adapter):
    spec = Spec(
        name="z3",
        family="SMT",
        language="SMT-LIB 2.6",
        emits="first-order constraints over theories (integers, reals, arrays, bit-vectors, strings, datatypes, quantifiers).",
        authority="satisfiability modulo those theories.",
        feedback="the solver transcript: sat/unsat/unknown per (check-sat), models from (get-model), unsat cores, error messages.",
        use="verification conditions, symbolic execution, invariants, policy checks, logic puzzles.",
        guidance=(
            "Send a complete, self-contained script with all declarations and at least one (check-sat). "
            "The verdict is the LAST (check-sat) result; an error before it makes the run an error. "
            "To PROVE a claim, assert the premises plus the NEGATION of the claim: unsat proves it by "
            "contradiction, sat gives a counterexample (add (get-model) to see it). "
            "For optimization use (maximize t)/(minimize t), then (check-sat) and (get-objectives): a bounded "
            "optimum is reported as optimal, with details.objectives."
        ),
        example=(
            "(declare-const x Int)\n(assert (> x 5))\n(assert (not (> (* 2 x) 10)))  ; negated claim\n(check-sat)"
        ),
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        code = _ECHO_VERDICT.sub(r'(echo "echo: \1")', unfence(code))
        if _OPTIMIZES.search(code) and "(get-objectives" not in code:
            code += "\n(get-objectives)"  # so a found optimum can be reported as optimal
        with workdir({"input.smt2": code}) as d:
            # -t: is a soft limit per query, so a hard (check-sat) answers `unknown` and the rest of the
            # script (get-info :reason-unknown, ...) still runs; -T: and the outer timeout are backstops.
            ms = max(1000, int(timeout * 1000))
            proc = sh(["z3", f"-t:{ms}", f"-T:{int(timeout) + 3}", "input.smt2"], cwd=d, timeout=timeout + 8)
        if proc.timed_out:
            return timed_out(proc)
        if proc.out.strip().splitlines()[-1:] == ["timeout"]:  # the hard limit hit: still "gave up", not an error
            return timed_out(proc, proc.out.strip()[: -len("timeout")])
        result = classify(proc.out, code)
        if result.verdict is Verdict.UNKNOWN and "timeout" in proc.out:
            result.details["timeout"] = True
        return hint(code, result)


ADAPTER = Z3()
