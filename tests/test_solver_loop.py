"""§4/§5 patterns against real backends (Docker). Models are scripted, tools are real."""

from __future__ import annotations

import pytest
from conftest import Fixed, ScriptedClient

from formalkit import LLM, Library, Trace, Verdict, backend, docker, observe, premises
from formalkit.patterns import (
    differential,
    houdini,
    instantiate,
    lean_equivalent,
    lns,
    probe,
    repair,
    smt_equivalent,
    soft_facts,
    suggest,
    tactic_swap,
    unique,
)
from formalkit.patterns.control import _mzn

pytestmark = pytest.mark.docker


def need(*names):
    missing = [n for n in names if not docker.has_image(n)]
    if missing:
        pytest.skip(f"images not built: {missing}")
    return [backend(n) for n in names]


def fenced(text):
    return (f"```\n{text}\n```", None)


# -- SMT: cores, premises, equivalence, uniqueness, differential, instantiation -------------


def test_unsat_core_names_the_conflict():
    (z3,) = need("z3")
    r = z3.run("""(set-option :produce-unsat-cores true)
(declare-const x Int)
(assert (! (> x 5) :named big))
(assert (! (< x 3) :named small))
(assert (! (> x -100) :named irrelevant))
(check-sat)
(get-unsat-core)""")
    assert r.verdict is Verdict.UNSAT and sorted(r.core) == ["big", "small"]


def test_premises_consistency_and_queries():
    (z3,) = need("z3")
    kb = premises(z3, "(declare-const age Int)\n(assert (>= age 18))")
    assert kb.consistent().verdict is Verdict.SAT
    assert kb.run("(assert (not (>= age 16)))\n(check-sat)").verdict is Verdict.UNSAT  # entailed: proved
    assert kb.run("(assert (> age 30))\n(check-sat)").verdict is Verdict.SAT  # merely consistent
    bad = premises(z3, "(set-option :produce-unsat-cores true)\n(declare-const a Int)\n"
                       "(assert (! (> a 1) :named lo))\n(assert (! (< a 0) :named hi))", check="(check-sat)\n(get-unsat-core)")
    r = bad.consistent()
    assert r.verdict is Verdict.UNSAT and sorted(r.core) == ["hi", "lo"]


def test_smt_equivalence():
    (z3,) = need("z3")
    a = "(declare-const x Int)\n(assert (> x 0))\n(assert (< x 5))"
    assert smt_equivalent(z3, a, "(declare-const x Int)\n(assert (and (>= x 1) (<= x 4)))").verdict is Verdict.PROVED
    r = smt_equivalent(z3, a, "(declare-const x Int)\n(assert (and (>= x 1) (<= x 5)))")
    assert r.verdict is Verdict.REFUTED and r.counterexample == {"x": "5"}


def test_uniqueness():
    (z3,) = need("z3")
    base = "(declare-const x Int)\n(declare-const y Int)\n(assert (= (+ x y) 10))\n(assert (> x y 0))\n"
    assert unique(z3, base + "(assert (= (- x y) 2))\n(check-sat)").verdict is Verdict.PROVED
    r = unique(z3, base + "(check-sat)")
    assert r.verdict is Verdict.REFUTED and r.counterexample != r.model


def test_differential_agreement():
    z3, cvc5 = need("z3", "cvc5")
    d = differential([z3, cvc5], "(declare-const x Int)\n(assert (> (* x x) 4))\n(assert (< x 3))\n(check-sat)")
    assert not d.disagree and {r.verdict for r in d.results.values()} == {Verdict.SAT}


QUANTIFIED = """(set-option :auto_config false)
(set-option :smt.mbqi false)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (! (P x) :pattern ((Q x)))))
(assert (not (P 7)))
(check-sat)"""


def test_instantiate_validates_every_instance():
    (z3,) = need("z3")
    assert z3.run(QUANTIFIED).verdict is Verdict.UNKNOWN  # e-matching never fires: z3 gives up
    llm = LLM(ScriptedClient([fenced("(assert (P 7))\n(assert (not (P 3)))")]), "m")
    out = instantiate(llm, z3, QUANTIFIED)
    assert out.accepted == ["(assert (P 7))"] and out.rejected == ["(assert (not (P 3)))"]
    assert out.result.verdict is Verdict.UNSAT and out.result.details["instances"] == ["(assert (P 7))"]


# -- ProbLog: model plausibilities, exact logic ------------------------------------------------


def test_soft_facts():
    (problog,) = need("problog")
    llm = LLM(ScriptedClient([('{"rain": 0.2}', None)]), "m")
    out = soft_facts(llm, problog, "?::rain.\n0.5::sprinkler.\nwet :- rain.\nwet :- sprinkler.\nquery(wet).")
    assert out.scores == {"rain": 0.2}
    assert out.result.model["wet"] == pytest.approx(1 - 0.8 * 0.5)


# -- MiniZinc: neighborhoods ---------------------------------------------------------------------


def test_lns_fixes_compile_in_minizinc():
    (mzn,) = need("minizinc")
    model = "var 0..10: x;\nvar 0..10: y;\narray[1..2] of var 0..5: a;\nconstraint x + y <= 12;\nsolve maximize x + y + sum(a);\n"
    fixes = "\n".join(f"constraint {k} = {_mzn(v)};" for k, v in {"x": 3, "a": [1, 2]}.items())
    r = mzn.run(model + fixes)
    assert r.verdict is Verdict.OPTIMAL and r.model["x"] == 3 and r.model["a"] == [1, 2] and r.model["y"] == 9


def test_lns_keeps_only_improvements():
    calls = []

    def fake(code):  # first solve: x=1 (obj 1); with x free, the neighborhood finds obj 5
        calls.append(code)
        fixed = "constraint x = 1;" in code
        value = 1 if len(calls) == 1 or fixed else 5
        return (Verdict.SAT, "", {"model": {"x": value, "_objective": value}, "objective": value})

    out = lns(lambda inc, hist: ["x"] if len(hist) == 0 else [], Fixed("minizinc", fake), "solve maximize x;", rounds=2)
    assert out.objective == 5 and out.result.verdict is Verdict.SAT and [h[1] for h in out.history] == [5, None]
    assert "constraint x = 1;" not in calls[1]  # round 1 frees x and finds 5
    assert len(calls) == 2 and out.empty == 1  # round 2 frees nothing: no pointless fully-fixed solve


# -- CBMC: Houdini over a pool of candidate invariants --------------------------------------------

PROGRAM = """int main(void) {
  int x = 0;
  while (x < 10) {
    /* CANDIDATES */
    x = x + 1;
  }
  __CPROVER_assert(x == 10, "post");
  return 0;
}"""


def test_houdini_with_cbmc():
    (cbmc,) = need("cbmc")

    def check(pairs):
        asserts = "\n    ".join(f'__CPROVER_assert({c}, "{label}");' for label, c in pairs)
        return cbmc.run(PROGRAM.replace("/* CANDIDATES */", asserts))

    out = houdini(["x >= 0", "x < 5", "x <= 10", "x == 0", "x != 11"], check)
    assert out.proved and out.kept == ["x >= 0", "x <= 10", "x != 11"]


# -- Lean: repair by tool correction, probing, library reuse, equivalence -------------------------


def test_lean_repair_by_tactic_swap():
    (lean,) = need("lean")
    code = "theorem t (a b : Nat) : a + b = b + a := by\n  rfl\n"
    first = lean.run(code)
    assert first.verdict is Verdict.ERROR
    steps = repair(lean, code, first, fixers=[tactic_swap(["simp", "omega"])])
    assert steps[-1].result.verdict is Verdict.PROVED and "omega" in steps[-1].arguments["code"]


def test_lean_probe_and_suggest():
    (lean,) = need("lean")
    trace = Trace()
    with observe(trace):
        root = lean.start("theorem t (n : Nat) (h : 2 < n) : 1 < n := by\n  sorry")
        outcomes = probe(root, ["omega", "rfl", "intro x"])
        ranked = suggest(root, lambda s: ["exact Nat.lt_trans (by decide) h", "omega", "nonsense_tactic"])
    assert outcomes["omega"] == "solved" and outcomes["rfl"] == "error"
    assert ranked and all(c.solved for c in ranked)
    assert {t["outcome"] for t in trace.tactics()} == {"solved", "error"} and trace.preferences()


def test_library_lemmas_are_usable_by_later_proofs():
    (lean,) = need("lean")
    lib = Library()
    lemma = "theorem my_double (n : Nat) : n + n = 2 * n := by omega"
    lib.add("my_double", lemma, lean.run(lemma))
    assert lib.entries["my_double"].proved
    with_lib = lib.attach(lean)
    assert with_lib.run("theorem use (k : Nat) : k + k = 2 * k := my_double k").verdict is Verdict.PROVED
    assert lean.run("theorem use (k : Nat) : k + k = 2 * k := my_double k").verdict is Verdict.ERROR


def test_lean_equivalence():
    (lean,) = need("lean")
    assert lean_equivalent(lean, "∀ n : ℕ, n + 0 = n", "∀ n : ℕ, 0 + n = n").verdict is Verdict.PROVED

