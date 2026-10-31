from __future__ import annotations

from formalkit.adapters._smtlib import unfence
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir


def normalize(text: str) -> "tuple[str, str]":
    """Re-derive the DIMACS header from the clauses; returns (cnf, note).

    The header only states counts, which models often get wrong (or omit);
    the clauses are what define the formula, so recompute them and say so.
    A malformed header (not 'p cnf <int> <int>') or a token that is not an
    integer is an error, not something to guess about.
    """
    clauses, current, declared, comments, headers = [], [], None, [], 0
    for n, raw in enumerate(unfence(text).splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("c"):
            comments.append(raw)
            continue
        if line.startswith("%"):  # SATLIB end marker
            break
        if line.startswith("p"):
            fields = line.split()
            if len(fields) != 4 or fields[1] != "cnf" or not (fields[2].isdigit() and fields[3].isdigit()):
                raise ValueError(f"line {n}: malformed header {line!r}; expected 'p cnf <variables> <clauses>'")
            declared, headers = line, headers + 1
            continue
        for token in line.split():
            try:
                lit = int(token)
            except ValueError:
                raise ValueError(
                    f"line {n}: {token!r} is not an integer literal (comment lines must start with 'c'; "
                    "clauses are integers ending in 0)"
                ) from None
            if lit == 0:
                clauses.append(current)
                current = []
            else:
                current.append(lit)
    note = []
    if current:
        clauses.append(current)
        note.append("the last clause was not terminated by 0; it was closed")
    if declared is None and not clauses:
        raise ValueError("empty input: no 'p cnf' header and no clauses")
    used = max((abs(x) for c in clauses for x in c), default=0)
    parts = declared.split() if declared else []
    declared_vars = int(parts[2]) if len(parts) == 4 and parts[1] == "cnf" and parts[2].isdigit() else 0
    header = f"p cnf {max(used, declared_vars)} {len(clauses)}"  # extra declared variables are legal
    if declared is None:
        note.append(f"no 'p cnf' header; used '{header}'")
    elif headers > 1:  # e.g. premises + query: one formula, one header
        note.append(f"combined {headers} 'p cnf' sections into '{header}'")
    elif parts != header.split():
        note.append(f"header '{declared}' did not match the clauses; used '{header}'")
    body = "\n".join(" ".join(map(str, c + [0])) for c in clauses)
    return "\n".join([*comments, header, body]) + "\n", "; ".join(note)


class Kissat(Adapter):
    spec = Spec(
        name="kissat",
        family="SAT",
        language="DIMACS CNF",
        emits="propositional constraints in conjunctive normal form (DIMACS).",
        authority="Boolean satisfiability; UNSAT answers come with a DRAT proof checked by drat-trim.",
        feedback="a satisfying assignment (true variables / false variables) or an independently checked unsatisfiability proof.",
        use="bounded search, finite puzzles, hardware-style and bit-blasted reasoning.",
        guidance=(
            "Write DIMACS: an optional 'c ...' comment block, a header 'p cnf <num_vars> <num_clauses>', then one "
            "clause per line as non-zero integers terminated by 0 (k = variable k true, -k = false). "
            "Keep a comment mapping variable numbers to meanings. sat returns details.model "
            "(variable -> true/false); unsat is certified when details.proof['checked'] is true. "
            "To PROVE a claim, add clauses for the NEGATION of the claim: unsat proves it."
        ),
        example="c 1 = rain, 2 = wet\np cnf 2 3\n-1 2 0\n1 0\n-2 0",
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        try:
            code, note = normalize(code)
        except ValueError as e:
            return Result(Verdict.ERROR, f"DIMACS parse error: {e}")
        result = self._solve(code, timeout)
        if note:
            result.output = f"note: {note}\n{result.output}"
            result.details["header_corrected"] = note
        return result

    def _solve(self, code: str, timeout: float) -> Result:
        with workdir({"input.cnf": code}) as d:
            proc = sh(
                # binary DRAT: about half the size of text proofs; drat-trim detects the format itself
                ["kissat", "-q", f"--time={max(1, int(timeout))}", "input.cnf", "proof.drat"],
                cwd=d,
                timeout=timeout + 5,
            )
            if proc.timed_out:
                return timed_out(proc)
            status = next((ln[2:].strip() for ln in proc.stdout.splitlines() if ln.startswith("s ")), None)
            if status == "SATISFIABLE":
                lits = [int(x) for ln in proc.stdout.splitlines() if ln.startswith("v ") for x in ln[2:].split()]
                assignment = {str(abs(v)): v > 0 for v in lits if v}
                true_vars = " ".join(k for k, v in assignment.items() if v) or "(none)"
                return Result(Verdict.SAT, f"s SATISFIABLE\ntrue variables: {true_vars}", {"model": assignment})
            if status == "UNSATISFIABLE":
                check = sh(["drat-trim", "input.cnf", "proof.drat"], cwd=d, timeout=timeout + 5)
                checked = "s VERIFIED" in check.stdout
                note = "DRAT proof verified by drat-trim" if checked else "DRAT proof NOT verified"
                return Result(Verdict.UNSAT, f"s UNSATISFIABLE\n{note}", {"proof": {"format": "DRAT", "checked": checked}})
            if status == "UNKNOWN":
                return timed_out(proc, proc.out)
        return Result(Verdict.ERROR, proc.out or f"kissat exited with code {proc.returncode}")


ADAPTER = Kissat()
