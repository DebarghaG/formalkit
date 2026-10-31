from __future__ import annotations

from formalkit.adapters._pyrunner import report, run_model_script
from formalkit.adapters._locate import locates
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter

# gurobi_persistent (not gurobi_direct) also accepts quadratic constraints (QCP/MIQCP).
SOLVERS = {"highs": "highs", "gurobi": "gurobi_persistent"}

# Uses Pyomo's new solver interface (pyomo.contrib.solver), which reports a
# uniform TerminationCondition + SolutionStatus across solvers.
RUNNER = r'''
import pyomo.environ as pyo
from pyomo.contrib.solver.common.factory import SolverFactory
if not isinstance(model, pyo.Block):
    emit({"error": "the script must assign a Pyomo model (pyo.ConcreteModel) to a top-level variable `model` "
                   "(found %s)" % type(model).__name__})
if isinstance(model, pyo.AbstractModel) and not model.is_constructed():
    emit({"error": "`model` is an AbstractModel without data: use pyo.ConcreteModel(), "
                   "or assign model = abstract.create_instance(data)"})
solver_name = sys.argv[2]
try:
    opt = SolverFactory(solver_name)
    if not opt.available():
        emit({"error": "solver %s is not available in this container (license?)" % solver_name})
    # Zero MIP gaps: "optimal" must mean optimal, not "within 0.01%" (solvers' default tolerance).
    res = opt.solve(model, time_limit=remaining(), load_solutions=False, rel_gap=0.0, abs_gap=0.0,
                    raise_exception_on_nonoptimal_result=False)
except BaseException as e:
    hint = ""
    if type(e).__name__ in ("IncompatibleModelError", "InvalidConstraintError"):
        hint = ("\nHiGHS solves linear models and convex quadratic objectives (no quadratic constraints, no "
                "sin/exp/log); Gurobi (solver='gurobi') also accepts quadratic constraints. Reformulate or linearize.")
    elif "size-limited license" in str(e):
        hint = "\nThe bundled Gurobi license is size-limited (2000 variables/constraints): use solver='highs'."
    emit({"error": brief(e) + hint})
tc, ss = res.termination_condition.name, res.solution_status.name
values = {}
if ss in ("feasible", "optimal"):
    res.solution_loader.load_vars()
    def shown(v):
        x = v.value
        if isinstance(x, float) and v.is_integer() and abs(x - round(x)) < 1e-6:
            return int(round(x))  # integer/binary variables: 3, not 2.9999999
        return x + 0.0 if isinstance(x, float) else x  # no -0.0
    values = {v.name: shown(v) for v in model.component_data_objects(pyo.Var, active=True)}
objs = list(model.component_data_objects(pyo.Objective, active=True))
emit({"termination": tc, "solution_status": ss, "objective": res.incumbent_objective,
      "bound": res.objective_bound, "has_objective": bool(objs),
      "sense": ("minimize" if objs[0].sense == pyo.minimize else "maximize") if objs else None,
      "values": values, "solver": "%s %s" % (res.solver_name, res.solver_version)})
'''


def _verdict(tc: str, ss: str, has_objective: bool) -> Verdict:
    """TerminationCondition + SolutionStatus -> verdict.

    Unbounded means the solver proved feasibility and an objective that
    improves without limit: solutions exist but no optimum, so SAT with
    details.unbounded. "infeasibleOrUnbounded" settles neither: UNKNOWN.
    """
    if tc == "convergenceCriteriaSatisfied" and ss == "optimal":
        return Verdict.OPTIMAL if has_objective else Verdict.SAT
    if tc == "provenInfeasible":
        return Verdict.UNSAT
    if tc == "unbounded":
        return Verdict.SAT
    if tc in ("error", "licensingProblems", "emptyModel", "invalidProblem"):
        return Verdict.ERROR
    if ss in ("feasible", "optimal"):  # stopped early (time/iteration/objective limit) with an incumbent
        return Verdict.SAT
    return Verdict.UNKNOWN


class Pyomo(Adapter):
    spec = Spec(
        name="pyomo",
        family="Mathematical programming",
        language="Python with Pyomo (solved by HiGHS, or Gurobi when licensed)",
        emits="an algebraic model in Pyomo: variables with bounds and domains, linear or quadratic constraints, "
        "and an objective.",
        authority="LP, MILP and convex QP solving: optimal solutions with bounds, or proofs of infeasibility.",
        feedback="the termination condition, objective value and dual bound, the value of every variable, "
        "your script's printed output, and Python tracebacks.",
        use="operations research, resource allocation, production planning, logistics, blending, network flows.",
        guidance=(
            "Write a Python script that builds a pyo.ConcreteModel and assigns it to a top-level variable "
            "named `model`. Do NOT call a solver - the tool solves it and reports every variable's value.\n"
            "Verdicts: optimal = solved to proven optimality (zero MIP gap); sat = a "
            "feasible solution but not proven optimal (time limit), or the objective is unbounded "
            "(details.unbounded = true: feasible, no optimum); unsat = proven infeasible, which PROVES the "
            "constraints are inconsistent; unknown = no decision (time ran out, or 'infeasible or unbounded'); "
            "error = the script raised an exception or the model is invalid (e.g. nonconvex/nonlinear for HiGHS).\n"
            "Optional `solver` input: 'highs' (default) or 'gurobi' (size-limited unless a license is mounted; "
            "needed for quadratic constraints)."
        ),
        example=(
            "import pyomo.environ as pyo\n"
            "model = pyo.ConcreteModel()\n"
            "model.x = pyo.Var(domain=pyo.NonNegativeIntegers)\n"
            "model.y = pyo.Var(domain=pyo.NonNegativeReals)\n"
            "model.c = pyo.Constraint(expr=2 * model.x + 3 * model.y <= 12)\n"
            "model.obj = pyo.Objective(expr=3 * model.x + 4 * model.y, sense=pyo.maximize)"
        ),
        inputs={"solver": "Optional: 'highs' (default) or 'gurobi'."},
        optional=["solver"],
    )

    @locates(())
    def run(self, code: str, timeout: float, solver: str = "", **inputs: str) -> Result:
        solver = (solver or "highs").strip().lower()
        if solver not in SOLVERS:
            return Result(Verdict.ERROR, f"unknown solver {solver!r}; choose one of {', '.join(SOLVERS)}")
        out = run_model_script(RUNNER + "\n", code, timeout, args=[SOLVERS[solver]])
        if isinstance(out, Result):
            return out
        data, printed = out
        tc, ss = data["termination"], data["solution_status"]
        verdict = _verdict(tc, ss, data["has_objective"])
        objective, bound = data["objective"], data["bound"]
        gap_left = (verdict is Verdict.OPTIMAL and objective is not None and bound is not None
                    and abs(objective - bound) > 1e-6 * max(1.0, abs(objective)))  # fmt: skip
        if gap_left:  # the solver stopped at a tolerance: a solution, not a proven optimum
            verdict = Verdict.SAT
        details = {k: data[k] for k in ("termination", "solution_status", "objective", "bound", "sense", "solver")}
        if data["values"] and verdict in (Verdict.SAT, Verdict.OPTIMAL):
            details["model"] = data["values"]
        extra = [f"termination: {tc}"]
        if tc == "unbounded":
            details["unbounded"] = True
            extra.append("the objective is unbounded: feasible solutions exist but there is no optimum")
        if data["bound"] is not None and data["objective"] is not None and verdict is Verdict.SAT:
            extra.append(f"best bound: {data['bound']}")
        if gap_left:
            extra.append("not proven optimal: the solver stopped with a gap between the objective and the best bound")
        shown_objective = None if verdict is Verdict.UNSAT or tc == "unbounded" else data["objective"]
        text = report(ss, shown_objective, data["values"], printed, tuple(extra))
        return Result(verdict, text, details)


ADAPTER = Pyomo()
