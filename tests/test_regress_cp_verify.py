"""Regressions found by real-world testing of the CP/MP and C-verifier backends (Docker)."""

from __future__ import annotations

import time

import pytest

from formalkit import Verdict, backend, docker

pytestmark = pytest.mark.docker


def need(name):
    if not docker.has_image(name):
        pytest.skip(f"image for {name} not built")
    return backend(name)


# -- MiniZinc -------------------------------------------------------------------------------


@pytest.mark.parametrize("solver", ["gecode", "chuffed"])
def test_minizinc_solver_int_limit_is_not_an_optimum(solver):
    r = need("minizinc").run("var int: x;\nconstraint x >= 0;\nsolve maximize x;", solver=solver)
    assert r.verdict is Verdict.SAT and r.details["unbounded"] and "integer limit" in r.output


def test_minizinc_bounded_optimum_is_still_optimal():
    r = need("minizinc").run("var 0..2000000000: x;\nsolve maximize x;")
    assert r.verdict is Verdict.OPTIMAL and r.details["objective"] == 2000000000 and "unbounded" not in r.details


# -- Python model scripts (cpmpy, pyomo) ------------------------------------------------------


def test_python_printed_output_is_clipped():
    r = need("cpmpy").run("import cpmpy as cp\nfor i in range(200000): print('line', i)\n"
                          "x=cp.intvar(0,3,name='x')\nmodel=cp.Model(x>=2)")  # fmt: skip
    assert r.verdict is Verdict.SAT and len(r.output) < 10000 and "omitted" in r.output and "line 199999" in r.output


def test_python_script_timeout_is_honored():
    start = time.monotonic()
    r = need("cpmpy").run("while True: pass", timeout=8)
    assert r.verdict is Verdict.UNKNOWN and time.monotonic() - start < 12


def test_python_slow_model_build_leaves_the_solver_the_rest():
    r = need("cpmpy").run("import time\ntime.sleep(5)\nimport cpmpy as cp\nx=cp.intvar(0,3,name='x')\n"
                          "model=cp.Model(x>=2)", timeout=10)  # fmt: skip
    assert r.verdict is Verdict.SAT


def test_pyomo_errors_are_concise_with_user_frames():
    r = need("pyomo").run("import pyomo.environ as pyo\ndef build():\n    m = pyo.ConcreteModel()\n    return m.y\n"
                          "model = build()")  # fmt: skip
    assert r.verdict is Verdict.ERROR and "line 4: return m.y" in r.output and "site-packages" not in r.output


def test_pyomo_nonlinear_model_gets_a_hint():
    r = need("pyomo").run("import pyomo.environ as pyo\nmodel=pyo.ConcreteModel()\nmodel.x=pyo.Var(bounds=(0,4))\n"
                          "model.o=pyo.Objective(expr=pyo.sin(model.x))")  # fmt: skip
    assert r.verdict is Verdict.ERROR and "HiGHS solves linear models" in r.output and "site-packages" not in r.output


# -- CBMC ------------------------------------------------------------------------------------

DEEP_BUG = "#include <assert.h>\nint main(void){ int x=0; for(int i=0;i<30;i++) x++; assert(x != 30); return 0; }"


def test_cbmc_depth_option_is_refused():
    r = need("cbmc").run("// cbmc: --depth 5\n" + DEEP_BUG)
    assert r.verdict is Verdict.ERROR and "--depth" in r.output
    assert need("cbmc").run(DEEP_BUG).verdict is Verdict.REFUTED


def test_cbmc_recursion_bound_is_unknown_not_refuted():
    r = need("cbmc").run("int nondet_int(void);\nint f(int n){ return n==0?0:1+f(n-1);}\n"
                         "int main(void){int n=nondet_int(); __CPROVER_assume(n>=0 && n<1000); return f(n);}")  # fmt: skip
    assert r.verdict is Verdict.UNKNOWN and r.goals and "counterexample" not in r.details


def test_cbmc_bodiless_function_is_an_input_error():
    r = need("cbmc").run("int foo(int);\nint main(void){ return foo(3); }")
    assert r.verdict is Verdict.ERROR and "foo" in r.output and "nondet_" in r.output


def test_cbmc_core_names_failing_labelled_assertions():
    r = need("cbmc").run('int main(void){ int x = 1; __CPROVER_assert(x == 2, "c0"); __CPROVER_assert(x == 1, "c1");'
                         ' __CPROVER_assert(x > 5, "c2"); return 0; }')  # fmt: skip
    assert r.verdict is Verdict.REFUTED and sorted(r.core) == ["c0", "c2"]


# -- ESBMC ------------------------------------------------------------------------------------

RACE = """#include <pthread.h>
#include <assert.h>
int x = 0;
void *t1(void *a){ x = 1; x = 2; x = 3; return 0; }
void *t2(void *a){ int y = x; assert(y != 2); return 0; }
int main(void){ pthread_t a, b; pthread_create(&a, 0, t1, 0); pthread_create(&b, 0, t2, 0);
  pthread_join(a,0); pthread_join(b,0); return 0; }"""


def test_esbmc_standard_headers_parse():
    code = "#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n#include <math.h>\n#include <pthread.h>\n" \
           "int main(void){ char *s = malloc(4); if (s) { strcpy(s, \"ab\"); free(s); } return 0; }"
    assert need("esbmc").run(code).verdict is Verdict.PROVED


def test_esbmc_finds_races_and_refuses_context_bounding():
    r = need("esbmc").run(RACE)
    assert r.verdict is Verdict.REFUTED and r.counterexample and r.core
    assert need("esbmc").run("// esbmc: --context-bound 1\n" + RACE).verdict is Verdict.ERROR


def test_esbmc_header_errors_are_reported():
    r = need("esbmc").run("#include <nonexistent_header.h>\nint main(void){return 0;}")
    assert r.verdict is Verdict.ERROR and "nonexistent_header.h" in r.output


# -- Frama-C ----------------------------------------------------------------------------------

LOOP = """/*@ requires 0 <= n <= 1000;
    ensures \\result == 2 * n; */
int dbl(int n){
  int i = 0, s = 0;
  /*@ CANDIDATES
      loop assigns i, s; */
  while (i < n) { i++; s += 2; }
  return s;
}"""


def test_framac_core_names_failing_invariants():
    r = need("framac").run(LOOP.replace("CANDIDATES", "loop invariant c0: 0 <= i <= n;\n      loop invariant c1: i < 0;"))
    assert r.verdict is Verdict.UNKNOWN and "c1" in r.core


def test_framac_houdini_over_acsl_invariants():
    from formalkit.patterns import houdini

    framac = need("framac")

    def check(pairs):
        invariants = "\n      ".join(f"loop invariant {label}: {c};" for label, c in pairs)
        return framac.run(LOOP.replace("CANDIDATES", invariants))

    out = houdini(["0 <= i <= n", "s == 2 * i", "i < 0", "s == i", "s >= 0"], check)
    assert out.proved and "s == 2 * i" in out.kept and "i < 0" not in out.kept and "s == i" not in out.kept


def test_framac_scoped_runs_say_so():
    r = need("framac").run("// framac: -wp-prop post_ok\n/*@ ensures post_ok: \\result == x; ensures bad: \\result == x + 1; */\n"
                           "int f(int x){ return x; }")  # fmt: skip
    assert r.verdict is Verdict.PROVED and r.details["scope"] == ["-wp-prop post_ok"] and "others were not" in r.output


# -- Ultimate Automizer ------------------------------------------------------------------------

NONDET = "extern int __VERIFIER_nondet_int(void);\n"


def test_ultimate_checks_plain_c_asserts():
    r = need("ultimate").run("#include <assert.h>\n" + NONDET +
                             "int main(void){ int x = __VERIFIER_nondet_int();\n  assert(x != 7);\n  return 0; }")  # fmt: skip
    assert r.verdict is Verdict.REFUTED and any("line 4" in step for step in r.counterexample)
    ok = need("ultimate").run("#include <assert.h>\n" + NONDET +
                              "int main(void){ int x = __VERIFIER_nondet_int(); if (x > 10) assert(x > 5); return 0; }")
    assert ok.verdict is Verdict.PROVED


def test_ultimate_requires_main():
    r = need("ultimate").run("int f(int x){ return x; }")
    assert r.verdict is Verdict.ERROR and "main" in r.output


# -- SV-COMP conventions across C verifiers -------------------------------------------------------

SV_PRE = """extern void abort(void);
void reach_error(void) {}
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
"""
SV = {
    "unsafe_counter": ("int main(void){ int x = 0; int n = __VERIFIER_nondet_int(); if (n < 0 || n > 20) return 0;"
                       " for (int i = 0; i < n; i++) x += 2; __VERIFIER_assert(x != 14); return 0; }", Verdict.REFUTED),
    "uint_wrap": ("int main(void){ unsigned int a = __VERIFIER_nondet_uint(); unsigned int b = a + 1;"
                  " if (a > 10) __VERIFIER_assert(b > a); return 0; }", Verdict.REFUTED),
    "safe_counter": ("int main(void){ int x = 0; int n = __VERIFIER_nondet_int(); if (n < 0 || n > 20) return 0;"
                     " for (int i = 0; i < n; i++) x += 2; __VERIFIER_assert(x == 2*n); return 0; }", Verdict.PROVED),
    "unbraced_else": ("int main(void){ int x = __VERIFIER_nondet_int(); if (x > 5) return 0; else if (x < -5) return 0;"
                      " else reach_error(); return 0; }", Verdict.REFUTED),
    "guarded_call": ("int main(void){ int x = __VERIFIER_nondet_int(); if (x > 5 && x < 3) reach_error(); return 0; }",
                     Verdict.PROVED),
}  # fmt: skip


@pytest.mark.parametrize("tool", ["cbmc", "esbmc", "ultimate"])
@pytest.mark.parametrize("case", sorted(SV))
def test_sv_comp_reach_error_is_the_property(tool, case):
    body, want = SV[case]
    r = need(tool).run(SV_PRE + body, timeout=120)
    assert r.verdict is want, r.output


# -- Pyomo / MiniZinc round 2 -------------------------------------------------------------------

QCP = ("import pyomo.environ as pyo\nmodel=pyo.ConcreteModel()\nmodel.x=pyo.Var(bounds=(0,5)); model.y=pyo.Var(bounds=(0,5))\n"
       "model.c=pyo.Constraint(expr=model.x**2 + model.y**2 <= 4)\nmodel.o=pyo.Objective(expr=model.x + model.y, sense=pyo.maximize)")


def test_pyomo_quadratic_constraints_with_gurobi():
    r = need("pyomo").run(QCP, solver="gurobi")
    assert r.verdict is Verdict.OPTIMAL and abs(r.details["objective"] - 2 * 2 ** 0.5) < 1e-4
    highs = need("pyomo").run(QCP)
    assert highs.verdict is Verdict.ERROR and "solver='gurobi'" in highs.output


def test_pyomo_abstract_model_is_explained():
    r = need("pyomo").run("import pyomo.environ as pyo\nmodel=pyo.AbstractModel()\nmodel.x=pyo.Var()\nmodel.o=pyo.Objective(expr=model.x)")
    assert r.verdict is Verdict.ERROR and "ConcreteModel" in r.output


def test_pyomo_gurobi_size_limit_hint():
    big = ("import pyomo.environ as pyo\nmodel=pyo.ConcreteModel()\nmodel.x=pyo.Var(range(3000), bounds=(0,1))\n"
           "model.o=pyo.Objective(expr=sum(model.x[i] for i in range(3000)), sense=pyo.maximize)")
    r = need("pyomo").run(big, solver="gurobi")
    assert r.verdict is Verdict.ERROR and "solver='highs'" in r.output


def test_minizinc_data_errors_name_the_data_input():
    r = need("minizinc").run("int: n;\nvar 1..n: x;\nsolve satisfy;", data="n = ;")
    assert r.verdict is Verdict.ERROR and "data input, line 1" in r.output


# -- runner robustness -------------------------------------------------------------------------


@pytest.mark.parametrize("prefix", [
    "import threading, time\nthreading.Thread(target=lambda: time.sleep(1000)).start()\n",  # lingering thread
    "import sys, io\nsys.stdout = io.StringIO()\n",  # replaced stdout
])  # fmt: skip
def test_python_runner_result_survives_hostile_scripts(prefix):
    start = time.monotonic()
    r = need("cpmpy").run(prefix + "import cpmpy as cp\nx=cp.intvar(0,3,name='x')\nmodel=cp.Model(x>=2)", timeout=20)
    assert r.verdict is Verdict.SAT and time.monotonic() - start < 10


# -- located errors (for patterns.repair / localize and learn.prefix_labels) -------------------------


@pytest.mark.parametrize("name,code,line", [
    ("minizinc", "var 1..3: x;\nconstraint x > ;\nsolve satisfy;", 2),
    ("cbmc", "int main(void){\n  int x = ;\n  return 0;\n}", 2),
    ("esbmc", "int main(void){\n  int x = ;\n  return 0;\n}", 2),
    ("framac", "int f(int x){\n  return x +;\n}", 2),
    ("ultimate", "int main(void){\n  int x = ;\n  return 0;\n}", 2),
    ("cpmpy", "import cpmpy as cp\nx = cp.intvar(0, 3)\nmodel = cp.Model(x // undefined_name)", 3),
    ("pyomo", "import pyomo.environ as pyo\nmodel = pyo.ConcreteModel()\nmodel.x = = 3", 3),
])  # fmt: skip
def test_errors_carry_source_lines(name, code, line):
    from formalkit.patterns import error_lines

    r = need(name).run(code, timeout=60)
    assert r.verdict is Verdict.ERROR and line in error_lines(r), (r.output, r.details.get("messages"))


def test_minizinc_solver_out_of_memory_is_explained():
    model = "array[1..200,1..200] of var 0..1: g;\nconstraint forall(i in 1..200)(sum(j in 1..200)(g[i,j]) = 1);\nsolve satisfy;"
    r = need("minizinc").run(model, timeout=60)
    assert r.verdict is Verdict.ERROR and "out of memory" in r.output and "chuffed" in r.output
    assert need("minizinc").run(model, timeout=60, solver="chuffed").verdict is Verdict.SAT


def test_python_memory_exhaustion_is_a_clean_error():
    start = time.monotonic()
    r = need("cpmpy").run("l = []\nwhile True: l.append(bytearray(10**8))", timeout=30)
    assert r.verdict is Verdict.ERROR and "MemoryError" in r.output and time.monotonic() - start < 20


def test_python_forked_children_do_not_delay_the_result():
    start = time.monotonic()
    r = need("cpmpy").run("import os\nfor i in range(10):\n    if os.fork() == 0:\n        import time; time.sleep(30); os._exit(0)\n"
                          "import cpmpy as cp\nx=cp.intvar(0,1,name='x')\nmodel=cp.Model(x==1)", timeout=40)  # fmt: skip
    assert r.verdict is Verdict.SAT and time.monotonic() - start < 10


def test_ultimate_floating_point_limit_is_unknown_not_error():
    r = need("ultimate").run(NONDET + "extern float __VERIFIER_nondet_float(void);\nint main(void){ float x = __VERIFIER_nondet_float();"
                             " if (x >= 0.0f && x <= 10.0f) __VERIFIER_assert(x * 2.0f >= 0.0f); return 0; }", timeout=120)  # fmt: skip
    assert r.verdict is Verdict.UNKNOWN and "cbmc or esbmc" in r.output


def test_minizinc_adds_a_missing_globals_include():
    model = "int: n = 6;\narray[1..n] of var 1..n: q;\nconstraint all_different(q);\nconstraint all_different([q[i] + i | i in 1..n]);\n" \
            "constraint all_different([q[i] - i | i in 1..n]);\nsolve satisfy;"
    r = need("minizinc").run(model)
    assert r.verdict is Verdict.SAT and r.details["included"] == "globals.mzn" and "has been added" in r.output
    bad = need("minizinc").run("var 1..3: x;\nconstraint no_such_predicate(x);\nsolve satisfy;")
    assert bad.verdict is Verdict.ERROR and "line 2" in bad.output  # still a real error, line numbers intact


def test_pyomo_integer_variables_are_reported_as_integers():
    r = need("pyomo").run("import pyomo.environ as pyo\nmodel=pyo.ConcreteModel()\nmodel.b=pyo.Var(domain=pyo.Binary)\n"
                          "model.n=pyo.Var(domain=pyo.NonNegativeIntegers, bounds=(0,9))\nmodel.y=pyo.Var(bounds=(0,2.5))\n"
                          "model.o=pyo.Objective(expr=model.b+model.n+model.y, sense=pyo.maximize)")  # fmt: skip
    assert r.model == {"b": 1, "n": 9, "y": 2.5} and isinstance(r.model["n"], int)


def test_cbmc_z3_backend_for_nonlinear_arithmetic():
    code = ("#include <assert.h>\nunsigned int nondet_uint(void);\n"
            "int main(void){ unsigned int n = nondet_uint(); unsigned int k = n * 0xAAAAAAABu; assert(3u * k == n); return 0; }")
    start = time.monotonic()
    assert need("cbmc").run("// cbmc: --z3\n" + code, timeout=60).verdict is Verdict.PROVED and time.monotonic() - start < 20
    slow = need("cbmc").run(code, timeout=8)
    assert slow.verdict is Verdict.UNKNOWN and "--z3" in slow.output
    bad = need("cbmc").run("// cbmc: --z3\n#include <assert.h>\nunsigned int nondet_uint(void);\n"
                           "int main(void){ unsigned int x = nondet_uint(); assert(x * x != 49u); return 0; }", timeout=60)
    assert bad.verdict is Verdict.REFUTED and bad.counterexample


@pytest.mark.parametrize("name,code", [
    ("cbmc", "// cbmc: --no-signed-overflow-check\n#include <assert.h>\nint nondet_int(void);\n"
             "int main(void){ int x = nondet_int(); assert(x == x); return x + 1; }"),
    ("esbmc", "// esbmc: --no-bounds-check\nint main(void){ int a[3]; int i = 3; a[i] = 1; return 0; }"),
    ("framac", "// framac: -wp-no-rte\n/*@ ensures \\\\result == x + 1; */\nint f(int x){ return x + 1; }"),
])  # fmt: skip
def test_disabled_checks_are_stated_on_proofs(name, code):
    r = need(name).run(code.replace("\\\\", "\\"), timeout=60)
    assert r.verdict is Verdict.PROVED and r.details["unchecked"] and "not verified" in r.output


def test_minizinc_integer_range_failure_is_explained():
    r = need("minizinc").run("var 1..2000000000: x;\nconstraint x * x > 5;\nsolve satisfy;")
    assert r.verdict is Verdict.ERROR and "integer range" in r.output and "memory" not in r.output.splitlines()[-1]


def test_esbmc_reports_real_bugs_hidden_behind_an_unwinding_failure():
    buggy = ("// esbmc: --unwind 3\nunsigned nondet_uint(void);\nint main(void){ unsigned a = nondet_uint(), b = nondet_uint();\n"
             "  while (nondet_uint()) { a = a * 3 + b; }\n  __ESBMC_assert(a != 77u, \"never\");\n  return 0; }")
    r = need("esbmc").run(buggy, timeout=60)
    assert r.verdict is Verdict.REFUTED and "within the loop bound" in r.output
    safe = ("// esbmc: --unwind 3\nint main(void){ int s = 0; for (int i = 0; i < 10; i++) s += i;\n"
            "  __ESBMC_assert(s == 45, \"sum\"); return 0; }")
    assert need("esbmc").run(safe, timeout=60).verdict is Verdict.UNKNOWN


def test_cbmc_unmodelled_library_function_is_explained():
    r = need("cbmc").run("#include <stdlib.h>\nint cmp(const void *a, const void *b){ return *(const int*)a - *(const int*)b; }\n"
                         "int main(void){ int a[3] = {3,1,2}; qsort(a, 3, sizeof(int), cmp); return 0; }")  # fmt: skip
    assert r.verdict is Verdict.ERROR and "no model of the library function(s) qsort" in r.output and "nondet_" not in r.output


def test_esbmc_internal_timeout_is_unknown_not_error():
    hard = (SV_PRE + "int main(){ unsigned int n = __VERIFIER_nondet_uint(); unsigned int d = __VERIFIER_nondet_uint();\n"
            "  if (d == 0u) d = 1u; __VERIFIER_assert(n % d < d); return 0; }")
    r = need("esbmc").run(hard, timeout=5)
    assert r.verdict in (Verdict.UNKNOWN, Verdict.PROVED) and (r.verdict is Verdict.PROVED or r.details.get("timeout"))


def test_esbmc_timeout_text_is_classified_unknown():
    from formalkit.adapters.esbmc import interpret

    r = interpret("ESBMC version 7.11.0\nParsing main.c\nRuntime decision procedure: 5.0s\nERROR: Timed out\n")
    assert r.verdict is Verdict.UNKNOWN and r.details["timeout"]


def test_minizinc_counts_all_solutions():
    m = need("minizinc")
    r = m.run("array[1..3] of var 0..10: x;\nconstraint sum(x) = 10;\nsolve satisfy;", all_solutions="true")
    assert r.verdict is Verdict.SAT and r.details["solutions_found"] == 66 and r.details["count_exact"] and "exactly 66" in r.output
    none = m.run("var 1..3: x;\nconstraint x > 5;\nsolve satisfy;", all_solutions="true")
    assert none.verdict is Verdict.UNSAT and "exactly 0" in none.output
    assert m.run("var 1..3: x;\nsolve maximize x;", all_solutions="true").verdict is Verdict.ERROR
    assert m.run("var 1..3: x;\nsolve satisfy;", all_solutions="true", solver="highs").verdict is Verdict.ERROR
    assert m.run("var 1..3: x;\nsolve satisfy;", all_solutions="true", solver="chuffed").details["solutions_found"] == 3


def test_cbmc_program_without_properties_is_not_proved():
    r = need("cbmc").run("int main(void){ int x = 3; return x; }")
    assert r.verdict is Verdict.UNKNOWN and "no properties" in r.output


HARD_KNAPSACK = """import pyomo.environ as pyo, random
r = random.Random(3)
n = 120
w = [r.randint(10**5, 10**6) for _ in range(n)]
v = [wi + r.randint(-1000, 1000) for wi in w]
model = pyo.ConcreteModel()
model.x = pyo.Var(range(n), domain=pyo.Binary)
model.c = pyo.Constraint(expr=sum(w[i]*model.x[i] for i in range(n)) <= sum(w)//2)
model.o = pyo.Objective(expr=sum(v[i]*model.x[i] for i in range(n)), sense=pyo.maximize)"""


@pytest.mark.parametrize("solver", ["highs", "gurobi"])
def test_pyomo_optimal_means_zero_gap(solver):
    r = need("pyomo").run(HARD_KNAPSACK, timeout=60, solver=solver)
    # With the solvers' default 1e-4 gap, both said "optimal" with different, suboptimal values.
    assert r.verdict is Verdict.OPTIMAL and r.details["objective"] == 34400217 == r.details["bound"]


def _zombies(name: str) -> int:
    import subprocess

    script = 'n=0; for p in /proc/[0-9]*; do grep -q "State:.*Z" $p/status 2>/dev/null && n=$((n+1)); done; echo $n'
    out = subprocess.run(["docker", "exec", f"formalkit-{name}", "sh", "-c", script], capture_output=True, text=True)
    return int(out.stdout.strip() or 0)


@pytest.mark.parametrize("name,code", [
    ("ultimate", NONDET + "int main(void){ int x = __VERIFIER_nondet_int(); if (x > 10) __VERIFIER_assert(x > 20); return 0; }"),
    ("cpmpy", "import os\nfor i in range(3):\n    if os.fork() == 0:\n        import time; time.sleep(30); os._exit(0)\n"
              "import cpmpy as cp\nx=cp.intvar(0,1,name='x')\nmodel=cp.Model(x==1)"),
])  # fmt: skip
def test_no_zombie_processes_accumulate(name, code):
    b = need(name)
    for _ in range(3):
        assert b.run(code, timeout=120).decisive
    time.sleep(1)
    assert _zombies(name) == 0


def test_cbmc_many_failing_properties_fall_back_to_the_first_violation():
    n = 300
    body = "\n".join(f"  a[{i}] = {i} / (b - {i});" for i in range(n))
    code = f"int nondet_int(void);\nint a[{n}];\nint main(void){{ int b = nondet_int();\n{body}\n  return 0; }}"
    start = time.monotonic()
    r = need("cbmc").run(code, timeout=40)
    assert r.verdict is Verdict.REFUTED and r.details["first_only"] and r.core and time.monotonic() - start < 45


def test_esbmc_mistyped_nondet_declaration_gets_a_hint():
    r = need("esbmc").run("extern int __VERIFIER_nondet_char(void);\nint main(void){ char c = __VERIFIER_nondet_char(); return c; }")
    assert r.verdict is Verdict.ERROR and "already declares" in r.output


def test_framac_allocation_gets_a_hint():
    r = need("framac").run("#include <stdlib.h>\nint f(void){ int *p = malloc(sizeof(int)); if (!p) return 0; *p = 1;"
                           " int r = *p; free(p); return r; }", timeout=60)  # fmt: skip
    assert r.verdict is Verdict.UNKNOWN and "cbmc or esbmc" in r.output
