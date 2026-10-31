from __future__ import annotations

import re
import time

from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

# SZS ontology -> formalkit verdicts. ContradictoryAxioms means the axioms
# alone are inconsistent, so the conjecture holds - but vacuously.
_SZS = {
    "Theorem": Verdict.PROVED,
    "ContradictoryAxioms": Verdict.PROVED,
    "Unsatisfiable": Verdict.UNSAT,
    "CounterSatisfiable": Verdict.REFUTED,
    "Satisfiable": Verdict.SAT,
    "InputError": Verdict.ERROR,
    "SyntaxError": Verdict.ERROR,
    "TypeError": Verdict.ERROR,
    "UsageError": Verdict.ERROR,
}
_STATUS_RE = re.compile(r"SZS status (\w+)")
_ANSWERS_RE = re.compile(r"^% SZS answers (.+?) for \S+\s*$", re.M)
_BLOCK_RE = re.compile(r"^% SZS output start (\w+).*?$(.*?)^% SZS output end", re.S | re.M)
_ERROR_RE = re.compile(r"(User error|Parsing Error|Parse error|error:)", re.I)


def _parse(out: str) -> Result:
    statuses = _STATUS_RE.findall(out)
    status = statuses[-1] if statuses else None
    blocks = {kind: body.strip() for kind, body in _BLOCK_RE.findall(out)}
    verdict = _SZS.get(status or "", Verdict.UNKNOWN)
    if status is None and _ERROR_RE.search(out):
        verdict = Verdict.ERROR
    details = {"szs_status": status, "szs_output": list(blocks)}
    # Proofs/refutations back proved & unsat; models and saturations are the
    # witnesses behind sat and (as countermodels) refuted.
    proofs = [b for k, b in blocks.items() if "Refutation" in k or "Proof" in k]
    witnesses = [b for k, b in blocks.items() if "Model" in k or "Saturation" in k]
    if proofs and verdict in (Verdict.PROVED, Verdict.UNSAT):
        details["proof"] = "\n\n".join(proofs)
    if witnesses and verdict in (Verdict.SAT, Verdict.REFUTED):
        details["model" if verdict is Verdict.SAT else "counterexample"] = "\n\n".join(witnesses)
    if verdict is Verdict.ERROR or not blocks:
        lines = [l for l in out.splitlines() if l.strip()]
        shown = "\n".join(lines[-60:])
    else:
        shown = "\n\n".join(f"% SZS output {kind}\n{body}" for kind, body in blocks.items())
    head = f"% SZS status {status}" if status else ""
    answers = _ANSWERS_RE.findall(out)
    if answers:  # a `question` was answered: the witness, e.g. Tuple [[W:=ann]|_]
        details["answers"] = answers[-1]
        head += f"\n% SZS answers {answers[-1]}"
    if status == "ContradictoryAxioms":
        details["vacuous"] = True
        head += "\nThe axioms alone are inconsistent, so the conjecture follows only vacuously: check the axioms."
    return Result(verdict, f"{head}\n{shown}".strip(), details)


_FORMULA_RE = re.compile(r"^\s*(?:fof|cnf|tff|thf|tcf)\s*\(", re.M)
_INCLUDE_RE = re.compile(r"^\s*include\s*\(", re.M)
_CONJECTURE_RE = re.compile(r"^\s*(?:fof|cnf|tff|thf|tcf)\s*\(\s*[^,]+,\s*(?:conjecture|question)\s*,", re.M)
_COMMENT_RE = re.compile(r"%[^\n]*|/\*.*?\*/", re.S)


def _precheck(code: str) -> str | None:
    """Reject inputs whose meaning would silently differ from what the writer intended."""
    text = _COMMENT_RE.sub("", code)
    if not _FORMULA_RE.search(text):
        return "no TPTP formulas found: write fof(name, role, formula). statements (or cnf/tff/thf)."
    if _INCLUDE_RE.search(text):
        return "include() is not supported (no TPTP library is installed): write the axioms inline."
    if len(_CONJECTURE_RE.findall(text)) > 1:
        return ("use exactly one conjecture or question: Vampire reads several as their DISJUNCTION. "
                "Combine them explicitly, e.g. fof(goal, conjecture, (p & q)).")  # fmt: skip
    return None


class Vampire(Adapter):
    spec = Spec(
        name="vampire",
        family="first-order ATP",
        language="TPTP (FOF, CNF or TFF)",
        emits="axioms, clauses and conjectures in TPTP syntax.",
        authority="first-order entailment (by refutation) and, for small problems, finite satisfiability.",
        feedback="the SZS status, plus the TPTP refutation proof, saturation, or finite model.",
        use="lemma proving, consistency checks of axiom sets, countermodel search.",
        guidance=(
            "Write a complete TPTP problem: fof(name, axiom, ...). and at most one fof(name, conjecture, ...). "
            "Variables are UPPERCASE, constants/predicates lowercase; quantifiers are ! [X] : and ? [X] :, "
            "connectives ~ & | => <=>. Verdicts: proved = the conjecture follows from the axioms (SZS Theorem; "
            "ContradictoryAxioms means the axioms are inconsistent, so the proof is vacuous: details.vacuous); refuted = the conjecture does NOT follow "
            "(CounterSatisfiable, often with a finite countermodel). Instead of a conjecture, a "
            "fof(q, question, ? [X] : p(X)). asks for a witness: proved, with details.answers like "
            "Tuple [[X:=a]|_]. Without a conjecture, unsat = the axioms are "
            "inconsistent and sat = they are consistent. unknown = gave up or timed out (not evidence either way). "
            "Arithmetic (tff with $int/$real) is supported but incomplete, especially nonlinear ($product of "
            "variables): for arithmetic-heavy claims prefer an SMT solver such as z3."
        ),
        example=(
            "fof(socrates_man, axiom, man(socrates)).\n"
            "fof(men_mortal, axiom, ! [X] : (man(X) => mortal(X))).\n"
            "fof(goal, conjecture, mortal(socrates))."
        ),
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        problem = _precheck(code)
        if problem:
            return Result(Verdict.ERROR, problem, {"szs_status": None})
        deadline = time.monotonic() + timeout
        with workdir({"problem.p": code}) as d:
            # Proving portfolio first; if it can't decide, try the
            # satisfiability (finite model building) portfolio with what's left.
            result = None
            for schedule in ("casc", "casc_sat"):
                left = deadline - time.monotonic()
                if left < 1 and result is not None:  # the proving portfolio always gets a run
                    break
                # uwa=off: Vampire 5.1.0's portfolio strategies with unification with abstraction
                # (uwa=alasca_main) "prove" false integer-arithmetic conjectures, e.g.
                # ![X:$int]: 0 = $difference(5, $sum(X, 4)) - found by differential fuzzing against z3.
                cmd = ["vampire", "--mode", "portfolio", "--schedule", schedule,
                       "--input_syntax", "tptp", "--proof", "tptp", "--forced_options", "uwa=off",
                       "-t", f"{max(1, int(left))}s", "problem.p"]  # fmt: skip
                proc = sh(cmd, cwd=d, timeout=left + 5)
                if proc.timed_out:
                    return result or timed_out(proc)
                result = _parse(proc.out.replace(f"{d}/", ""))
                if result.verdict is not Verdict.UNKNOWN:
                    break
        return result


ADAPTER = Vampire()
