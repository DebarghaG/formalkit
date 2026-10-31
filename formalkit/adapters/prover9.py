from __future__ import annotations

import re

from formalkit.adapters._ladr import errors, goal_count, sections
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

# Prover9 exit codes (LADR manual, "Prover9 exit codes").
_EXIT = {
    0: ("proof found", Verdict.PROVED),
    1: ("fatal error", Verdict.ERROR),
    2: ("sos empty: search space exhausted without a proof", Verdict.UNKNOWN),
    3: ("max_megs reached", Verdict.UNKNOWN),
    4: ("max_seconds reached", Verdict.UNKNOWN),
    5: ("max_given reached", Verdict.UNKNOWN),
    6: ("max_kept reached", Verdict.UNKNOWN),
    7: ("action exit", Verdict.UNKNOWN),
    101: ("interrupted", Verdict.UNKNOWN),
    102: ("crashed", Verdict.ERROR),
}


class Prover9(Adapter):
    spec = Spec(
        name="prover9",
        family="first-order ATP",
        language="Prover9/LADR input",
        emits="first-order assumptions and goals in Prover9 syntax.",
        authority="first-order entailment with equality, by resolution/paramodulation refutation.",
        feedback="the exit status and, on success, the numbered resolution proof.",
        use="lemma proving, equational and algebraic reasoning.",
        guidance=(
            "Write formulas(assumptions). ... end_of_list. and formulas(goals). ... end_of_list. "
            "Any name starting with u-z (x, y, w, user...) is a VARIABLE, implicitly universal: name constants "
            "with a-t (e.g. westworld, c1, alice). Bind variables explicitly with "
            "all x / exists x. Connectives: - (not), & , |, ->, <->; every formula ends with a period. "
            "proved = all goals follow from the assumptions (details.vacuous when the assumptions themselves are "
            "contradictory); without goals, unsat = the assumptions are contradictory. unknown = no proof found (timeout, limits, or "
            "'sos empty' - an exhausted search suggests but does not prove the goal is false; use mace4 to "
            "find a countermodel). error = syntax error, with the offending input quoted."
        ),
        example=(
            "formulas(assumptions).\n  man(socrates).\n  man(x) -> mortal(x).\nend_of_list.\n\n"
            "formulas(goals).\n  mortal(socrates).\nend_of_list."
        ),
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        # Mace4-only options (domain sizes, model counts...) are ignored, with a
        # note, like `mace4 -c` does for Prover9-only ones: the same input can go
        # to both tools, e.g. portfolio(prover9, mace4).
        ignored: list = []
        while True:
            script = f"assign(max_seconds, {max(1, int(timeout))}).\n{code}"
            with workdir({"input.in": script}) as d:
                proc = sh(["prover9", "-f", "input.in"], cwd=d, timeout=timeout + 5)
            command = _unrecognized_option(proc.out)
            if proc.timed_out or command is None or len(ignored) >= 20:
                break
            stripped = _drop_command(code, command)
            if stripped == code:
                break
            code = stripped
            ignored.append(command)
        if proc.timed_out:
            return timed_out(proc, "prover9 timed out")
        reason, verdict = _EXIT.get(proc.returncode, (f"exit code {proc.returncode}", Verdict.ERROR))
        proofs = [body for title, body in sections(proc.stdout) if title == "PROOF"]
        details = {"exit": reason}
        # The exit code alone is not the verdict: auto mode may raise max_proofs (e.g. for a Horn set
        # with several negative clauses) and then stop with "sos empty" after the proof that matters.
        if proofs and verdict is not Verdict.ERROR:
            verdict, reason = _judge(code, proofs)
            details["exit"] = reason
            if verdict is Verdict.PROVED and "contradictory" in reason:
                details["vacuous"] = True
        if ignored:
            details["ignored"] = ignored
        if proofs and verdict is Verdict.PROVED:
            details["proof"] = "\n\n".join(proofs)
        if verdict is Verdict.ERROR:
            shown = errors(proc.out) or proc.out[-3000:]
        elif proofs:
            shown = "\n\n".join(proofs)
        else:
            stats = [body for title, body in sections(proc.stdout) if title == "STATISTICS"]
            shown = stats[-1] if stats else ""
        note = f"ignored options Prover9 does not know: {' '.join(ignored)}\n" if ignored else ""
        return Result(verdict, f"{note}{reason}\n{shown}".strip(), details)


_GOAL_LINE_RE = re.compile(r"^\d+\s+(.*?)\s+#.*\[goal\]\.\s*$", re.M)


def _judge(code: str, proofs: list) -> tuple:
    """The verdict from the proofs found, not from Prover9's exit code."""
    goals = goal_count(code)
    if any(not _GOAL_LINE_RE.search(p) for p in proofs):  # a refutation that never used a goal
        if goals == 0:
            return Verdict.UNSAT, "the assumptions are contradictory (a refutation without any goal)"
        return Verdict.PROVED, "proof found - but the assumptions are contradictory, so it is vacuous"
    proved = {g for p in proofs for g in _GOAL_LINE_RE.findall(p)}
    if len(proved) >= goals:
        return Verdict.PROVED, "proof found"
    return Verdict.UNKNOWN, f"proved {len(proved)} of {goals} goals (all must follow)"


_UNRECOGNIZED_RE = re.compile(r"%%ERROR: (?:Parameter|Flag) not recognized:.*?%%START ERROR%%\s*(.*?)\s*%%END ERROR%%", re.S)


def _unrecognized_option(out: str) -> str | None:
    match = _UNRECOGNIZED_RE.search(out)
    return match.group(1).strip() if match else None


def _drop_command(code: str, command: str) -> str:
    """``code`` without the first statement equal to ``command`` (whitespace-insensitive)."""
    target = re.sub(r"\s+", "", command)
    lines = code.split("\n")
    for i, line in enumerate(lines):
        if re.sub(r"\s+", "", line) == target:
            return "\n".join(lines[:i] + lines[i + 1 :])
    return code


ADAPTER = Prover9()
