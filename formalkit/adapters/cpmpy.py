from __future__ import annotations

from formalkit.adapters._pyrunner import report, run_model_script
from formalkit.adapters._locate import locates
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter

RUNNER = r'''
import cpmpy as cp
from cpmpy.transformations.get_variables import get_variables_model
if not isinstance(model, cp.Model):
    emit({"error": "the script must assign a cpmpy.Model to a top-level variable `model` (found %s)"
                   % type(model).__name__})
try:
    model.solve(solver="ortools", time_limit=remaining())
except BaseException as e:
    emit({"error": brief(e)})
status = model.status().exitstatus.name
found = status in ("OPTIMAL", "FEASIBLE")
values = {str(v): v.value() for v in get_variables_model(model)} if found else {}
values = {k: (bool(x) if type(x).__name__ in ("bool", "bool_") else x) for k, x in values.items()}
emit({"status": status, "has_objective": model.has_objective(), "values": values,
      "objective": model.objective_value() if found and model.has_objective() else None,
      "runtime": model.status().runtime})
'''

# CP-SAT says FEASIBLE for solved satisfaction problems and OPTIMAL only with
# an objective; guard anyway so OPTIMAL never appears without one.
_STATUS = {"FEASIBLE": Verdict.SAT, "UNSATISFIABLE": Verdict.UNSAT}


class CPMpy(Adapter):
    spec = Spec(
        name="cpmpy",
        family="Constraint programming",
        language="Python with CPMpy (solved by OR-Tools CP-SAT)",
        emits="a Python script declaring CPMpy variables with finite domains, constraints and an optional objective.",
        authority="feasible or optimal assignments, decided by OR-Tools CP-SAT.",
        feedback="the solver status, objective value, the value of every variable in the model, your script's "
        "printed output, and Python tracebacks.",
        use="scheduling, routing, timetabling, assignment, puzzles - anything with integer/Boolean decisions.",
        guidance=(
            "Write a Python script that builds a cpmpy.Model and assigns it to a top-level variable named "
            "`model`. Do NOT call model.solve() - the tool solves it with CP-SAT and reports the value of every "
            "variable, so give variables meaningful names (cp.intvar(0, 10, name='start')). To count solutions, "
            "you may call `print(model.solveAll())` yourself (it returns the number of solutions); the verdict "
            "still comes from solving `model`.\n"
            "Verdicts: sat = a solution was found (for optimization: not proven optimal before the time limit); "
            "optimal = proven optimal; unsat = no solution exists, which PROVES the constraints are inconsistent "
            "(to prove a claim, add its negation as a constraint and get unsat); unknown = time ran out; "
            "error = the script raised an exception or defined no `model`."
        ),
        example=(
            "import cpmpy as cp\n"
            "x = cp.intvar(1, 9, shape=3, name='x')\n"
            "model = cp.Model(cp.AllDifferent(x), x[0] + x[1] == x[2], minimize=x[2])"
        ),
    )

    @locates(())
    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        out = run_model_script(RUNNER, code, timeout)
        if isinstance(out, Result):
            return out
        data, printed = out
        status = data["status"]
        if status == "OPTIMAL":
            verdict = Verdict.OPTIMAL if data["has_objective"] else Verdict.SAT
        else:
            verdict = _STATUS.get(status, Verdict.UNKNOWN)
        details = {k: data[k] for k in ("status", "objective", "runtime")}
        if data["values"] and verdict in (Verdict.SAT, Verdict.OPTIMAL):
            details["model"] = data["values"]
        return Result(verdict, report(status, data["objective"], data["values"], printed), details)


ADAPTER = CPMpy()
