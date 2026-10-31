from __future__ import annotations

import json
import re
import shutil
import time

from formalkit.adapters._locate import locates
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

SOLVERS = ("gecode", "chuffed", "highs", "cbc")

# MiniZinc status -> verdict. UNBOUNDED means feasible with no optimum, so a
# solution exists (SAT); UNSAT_OR_UNBOUNDED settles neither, so UNKNOWN.
_STATUS = {
    "OPTIMAL_SOLUTION": Verdict.OPTIMAL,
    "ALL_SOLUTIONS": Verdict.SAT,
    "SATISFIED": Verdict.SAT,
    "UNBOUNDED": Verdict.SAT,
    "UNSATISFIABLE": Verdict.UNSAT,
    "UNSAT_OR_UNBOUNDED": Verdict.UNKNOWN,
    "UNKNOWN": Verdict.UNKNOWN,
    "ERROR": Verdict.ERROR,
}


# CP solvers bound `var int` internally. An "optimum" sitting exactly on that bound is an
# artifact of the solver, not of the model: the objective is (almost surely) unbounded.
_INT_LIMIT = {"gecode": 2147483646, "chuffed": 500000000}


def _at_limit(value, limit: int) -> bool:
    if isinstance(value, bool):
        return False
    if isinstance(value, int):
        return abs(value) >= limit
    if isinstance(value, list):
        return any(_at_limit(v, limit) for v in value)
    if isinstance(value, dict):
        return any(_at_limit(v, limit) for v in value.values())
    return False


def _memory_cap() -> list:
    """Run the solver under an address-space cap (75% of the container's memory).

    A solver that exhausts memory then fails cleanly with a message, instead of
    being OOM-killed silently and starving every other run in the container.
    """
    try:
        limit = int(open("/sys/fs/cgroup/memory.max").read().strip())
    except (OSError, ValueError):  # "max" (no limit) or no cgroup v2
        return []
    if not shutil.which("prlimit"):
        return []
    return ["prlimit", f"--as={int(limit * 0.75)}", "--"]


def _location(msg: dict) -> str:
    loc = msg.get("location") or {}
    if "firstLine" not in loc:
        return ""
    where = "data input, " if str(loc.get("filename", "")).endswith("data.dzn") else ""
    return f"{where}line {loc['firstLine']}, col {loc['firstColumn']}: "


class MiniZinc(Adapter):
    spec = Spec(
        name="minizinc",
        family="Constraint programming",
        language="MiniZinc",
        emits="variables with finite domains, constraints, and an optional objective (solve satisfy / minimize / maximize).",
        authority="feasible or optimal assignments, decided by a CP or MIP solver.",
        feedback="the status, the best solution found (as JSON, with _objective), and compiler errors with line numbers.",
        use="scheduling, routing, timetabling, assignment and packing problems.",
        guidance=(
            "Send a complete MiniZinc model. Put instance data either in the model or in the optional `data` "
            "input (.dzn syntax). Every non-output variable is reported in the solution JSON.\n"
            "Verdicts: sat = a solution was found (for optimization: not proven optimal, or the objective is "
            "unbounded - see details.unbounded); optimal = proven optimal; unsat = no solution exists, which "
            "PROVES the constraints are inconsistent (use this to prove a claim: add its negation as a "
            "constraint); unknown = time ran out before anything was decided; error = the model did not compile. "
            "To COUNT solutions of a `solve satisfy` model, set the `all_solutions` input to 'true'.\n"
            f"Optional `solver` input: one of {', '.join(SOLVERS)} (default gecode; chuffed is a strong "
            "lazy-clause CP solver; highs/cbc are MIP solvers, good for linear models with floats)."
        ),
        example=(
            "array[1..3] of var 1..9: x;\n"
            "constraint x[1] + x[2] + x[3] = 15 /\\ x[1] < x[2] /\\ x[2] < x[3];\n"
            "solve maximize x[1] * x[3];"
        ),
        inputs={
            "data": "Optional MiniZinc data (.dzn) for the model.",
            "solver": f"Optional solver: {', '.join(SOLVERS)}. Default: gecode.",
            "all_solutions": "Optional: 'true' to enumerate every solution of a satisfaction problem "
            "(details.solutions_found is the count; exact only if the status is ALL_SOLUTIONS).",
        },
        optional=["data", "solver", "all_solutions"],
    )

    @locates(("data input",))
    def run(self, code: str, timeout: float, data: str = "", solver: str = "", all_solutions: str = "",
            **inputs: str) -> Result:
        solver = (solver or "gecode").strip().lower()
        if solver not in SOLVERS:
            return Result(Verdict.ERROR, f"unknown solver {solver!r}; choose one of {', '.join(SOLVERS)}")
        deadline = time.monotonic() + timeout
        enumerate_all = str(all_solutions).strip().lower() in ("true", "1", "yes")
        if enumerate_all and solver in ("highs", "cbc"):
            return Result(Verdict.ERROR, f"all_solutions needs a CP solver: {solver} (a MIP solver) returns a single "
                          "solution. Use solver 'gecode' (the default) or 'chuffed'.")
        if enumerate_all and re.search(r"\bsolve\b[^;]*\b(minimize|maximize)\b", code):
            return Result(Verdict.ERROR, "all_solutions counts solutions of satisfaction problems (`solve satisfy;`); "
                          "for an optimization model, constrain the objective to its optimum and enumerate that.")
        result = self._solve(code, data, solver, timeout, enumerate_all)
        # The most common slip: a global constraint (all_different, cumulative, ...) used without
        # `include "globals.mzn";`. Retry once with it on line 1, so line numbers stay put.
        if result.verdict is Verdict.ERROR and "no function or predicate with name" in result.output \
                and "globals.mzn" not in code and deadline - time.monotonic() > 2:
            retry = self._solve('include "globals.mzn"; ' + code, data, solver, deadline - time.monotonic(), enumerate_all)
            if "no function or predicate with name" not in retry.output:
                retry.output += '\nnote: `include "globals.mzn";` was missing and has been added for you.'
                retry.details["included"] = "globals.mzn"
                return retry
        return result

    def _solve(self, code: str, data: str, solver: str, timeout: float, enumerate_all: bool = False) -> Result:
        files = {"model.mzn": code}
        if data.strip():
            files["data.dzn"] = data
        cmd = [
            *_memory_cap(),
            "minizinc", "--solver", solver, "--json-stream", "--output-mode", "json", "--output-objective",
            "--time-limit", str(int(max(1.0, timeout - 2) * 1000)), "model.mzn",
        ]  # fmt: skip
        if "data.dzn" in files:
            cmd.append("data.dzn")
        if enumerate_all:
            cmd.append("--all-solutions")
        with workdir(files) as d:
            proc = sh(cmd, cwd=d, timeout=timeout + 10)
        if proc.timed_out:
            return timed_out(proc)
        return self._parse(proc.stdout, proc.stderr, solver, enumerate_all)

    @staticmethod
    def _parse(stdout: str, stderr: str, solver: str, enumerate_all: bool = False) -> Result:
        solution, status, solutions, every = None, None, 0, []
        errors, warnings, other = [], [], []
        for line in stdout.splitlines():
            try:
                msg = json.loads(line)
            except ValueError:
                if line.strip():
                    other.append(line.strip())
                continue
            kind = msg.get("type")
            if kind == "solution":
                solution, solutions = (msg.get("output") or {}).get("json"), solutions + 1
                if enumerate_all and len(every) < 100:
                    every.append(solution)
            elif kind == "status":
                status = msg.get("status")
            elif kind == "error":
                errors.append(f"{msg.get('what', 'error')}: {_location(msg)}{msg.get('message', '')}")
            elif kind == "warning":
                warnings.append(f"warning: {_location(msg)}{msg.get('message', '')}")
        for line in stderr.splitlines():
            if line.strip() and "--time-out flag has recently been changed" not in line:
                other.append(line.strip())

        if errors or status == "ERROR":
            verdict = Verdict.ERROR
        elif status:
            verdict = _STATUS.get(status, Verdict.UNKNOWN)
        else:  # satisfaction problems end after the first solution with no status line
            verdict = Verdict.SAT if solution is not None else Verdict.UNKNOWN

        details = {"status": status or ("SATISFIED" if solution is not None else None), "solver": solver,
                   "solutions_found": solutions}  # fmt: skip
        if solution is not None and verdict in (Verdict.SAT, Verdict.OPTIMAL):
            details["model"] = solution
        if isinstance(solution, dict) and "_objective" in solution:
            details["objective"] = solution["_objective"]
        if status == "UNBOUNDED":
            details["unbounded"] = True
        if enumerate_all:
            details["solutions"] = every  # the first 100
            details["count_exact"] = status in ("ALL_SOLUTIONS", "UNSATISFIABLE")
        limit = _INT_LIMIT.get(solver)
        suspect = limit is not None and verdict is Verdict.OPTIMAL and _at_limit(solution, limit)
        if suspect:
            verdict = Verdict.SAT
            details["unbounded"] = True

        lines = [f"status: {details['status'] or 'none'}"]
        if suspect:
            lines.append(
                f"warning: the solution reaches {solver}'s integer limit (±{limit}), so this is not a real optimum: "
                "the objective is most likely unbounded. Give every `var int` explicit bounds (e.g. var 0..1000)."
            )
        if enumerate_all:
            exact = status in ("ALL_SOLUTIONS", "UNSATISFIABLE")  # unsat: exactly zero
            lines.append(f"{'exactly' if exact else 'at least'} {solutions} solution(s)"
                         + ("" if exact else " (enumeration did not finish)"))
        if solution is not None:
            lines.append(("last " if enumerate_all else "") + "solution: " + json.dumps(solution))
        lines += errors + warnings + other
        if verdict is Verdict.ERROR and not errors:
            # The solver itself failed (no compile error was reported).
            text = "\n".join(other)
            alternatives = ", ".join(s for s in SOLVERS if s != solver)
            if "out of range" in text:
                why = (" because a value exceeds its integer range: give variables smaller bounds, or use "
                       "highs/cbc for large numbers")
            elif any(k in text for k in ("MemoryExhausted", "bad_alloc", "emory")):
                why = " by running out of memory"
            elif "rror" in text:
                why = " (see its messages above)"
            else:
                why = " without an error message (most often it ran out of memory)"
            lines.append(f"the {solver} solver failed{why}; try another solver ({alternatives}) or a smaller model.")
        return Result(verdict, "\n".join(lines), details)


ADAPTER = MiniZinc()
