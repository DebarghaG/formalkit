from __future__ import annotations

import time

from formalkit.adapters._smtlib import classify, hint, unfence
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir


class Cvc5(Adapter):
    spec = Spec(
        name="cvc5",
        family="SMT",
        language="SMT-LIB 2.6",
        emits="first-order constraints over theories (integers, reals, arrays, bit-vectors, strings, sequences, sets, datatypes, quantifiers).",
        authority="satisfiability modulo those theories.",
        feedback="the solver transcript: sat/unsat/unknown per (check-sat), models from (get-model), unsat cores, error messages.",
        use="verification conditions, string and set constraints, quantified problems, cross-checking Z3.",
        guidance=(
            "Send a complete, self-contained script with all declarations and at least one (check-sat). "
            "Models are enabled, so (get-model) works after sat; for (get-unsat-core) add "
            "(set-option :produce-unsat-cores true) and name assertions with (! ... :named n). "
            "The verdict is the LAST (check-sat) result; cvc5 stops at the first error, which makes the run an error. "
            "To PROVE a claim, assert the premises plus the NEGATION of the claim: unsat proves it by "
            "contradiction, sat gives a counterexample."
        ),
        example=(
            "(set-logic ALL)\n(declare-const s String)\n(assert (str.prefixof \"ab\" s))\n"
            "(assert (not (>= (str.len s) 2)))  ; negated claim\n(check-sat)"
        ),
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        ms = max(1000, int(timeout * 1000))
        code = unfence(code)
        started = time.monotonic()
        with workdir({"input.smt2": code}) as d:
            # --incremental: push/pop and several (check-sat)s, as with z3.
            proc = sh(["cvc5", "-q", "--produce-models", "--incremental", f"--tlimit-per={ms}", "input.smt2"],
                      cwd=d, timeout=timeout + 5)
        if proc.timed_out or "interrupted by timeout" in proc.out:
            return timed_out(proc)
        result = classify(proc.out, code)
        if result.verdict is Verdict.UNKNOWN and time.monotonic() - started >= 0.9 * timeout:
            result.details["timeout"] = True  # cvc5 says only `unknown` when --tlimit-per runs out
        return hint(code, result)


ADAPTER = Cvc5()
