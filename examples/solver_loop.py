"""§4 solver-in-the-loop patterns, end to end, with a real model.

    OPENAI_BASE_URL=https://api.deepseek.com OPENAI_API_KEY=... MODEL=deepseek-flash \\
        python examples/solver_loop.py [decompose repair route instantiate soft houdini library]
"""

import os
import sys

from openai import OpenAI

import formalkit
from formalkit.patterns import (
    AUTOMATION,
    decompose,
    houdini,
    instantiate,
    repair,
    route,
    soft_facts,
    tactic_swap,
)

llm = formalkit.LLM(OpenAI(), os.environ.get("MODEL", "gpt-5"), max_tokens=8192)


def show(title, value):
    print(f"\n=== {title}\n{value}", flush=True)


def run_decompose():
    """POETRY / DeepSeek-Prover-V2: sketch with `have ... := by sorry`, recurse into the holes."""
    lean = formalkit.backend("lean")
    theorem = (
        "import Mathlib\n\ntheorem sum_odds (n : ℕ) :\n"
        "    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by\n  sorry\n"
    )
    trace = formalkit.Trace()
    with formalkit.observe(trace):
        out = decompose(llm, lean, theorem, depth=2, width=2)
    show("decompose", f"proved={out.proved}  ({len(trace)} events)\n{out.code if out.proved else out.result.feedback()}")


def run_repair():
    """Baldur / Lyra: symbolic tool correction first, then the model with a localized error."""
    lean = formalkit.backend("lean")
    broken = "import Mathlib\n\ntheorem t (a b : ℕ) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by\n  exact Nat.pow_le_pow h 2\n"
    steps = repair(lean, broken, fixers=[tactic_swap(AUTOMATION["lean"])], llm=llm)
    show("repair", " -> ".join(str(s.result.verdict) for s in steps) + "\n" + steps[-1].arguments["code"])


def run_route():
    """Adaptive formalism selection: the model picks the backend for each problem."""
    backends = formalkit.backends("z3", "clingo", "prolog", "minizinc")
    problems = {
        "puzzle": "Find all ways to place 4 non-attacking queens on a 4x4 board.",
        "optimize": "Choose integer quantities of 3 products to maximize profit under resource limits.",
        "rules": "Given parent facts, list everyone's ancestors.",
        "arith": "Is there a real x with x^2 - 2x + 5 = 0?",
    }
    show("route", {k: route(llm, p, backends).name for k, p in problems.items()})


def run_instantiate():
    """AquaForte: the model proposes quantifier instances; z3 validates each before use."""
    z3 = formalkit.backend("z3")
    script = """(set-option :auto_config false)
(set-option :smt.mbqi false)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun h (Int) Int)
(assert (forall ((x Int)) (! (= (f (g x)) (+ x 1)) :pattern ((h x)))))
(assert (not (= (f (g 41)) 42)))
(check-sat)"""
    out = instantiate(llm, z3, script)
    show("instantiate", f"{out.result.verdict}  accepted={out.accepted}  rejected={out.rejected}")


def run_soft():
    """OrLog: the model judges atoms, ProbLog does the logic exactly."""
    problog = formalkit.backend("problog")
    program = """?::flies(tweety).
?::penguin(tweety).
can_travel_far(X) :- flies(X).
query(can_travel_far(tweety)).
"""
    out = soft_facts(llm, problog, program, context="Tweety is a small yellow canary.")
    show("soft_facts", f"scores={out.scores}  result={out.result.model}")


def run_houdini():
    """Kamath et al.: pool invariant candidates from several samples, let CBMC prune them."""
    cbmc = formalkit.backend("cbmc")
    program = """int main(void) {
  int i = 0, s = 0;
  while (i < 20) {
    /* CANDIDATES */
    s = s + 2;
    i = i + 1;
  }
  __CPROVER_assert(s == 40, "post");
  return 0;
}"""
    replies = llm.ask(
        f"Propose 6 candidate loop invariants (C boolean expressions over i and s) for:\n{program}\n"
        "One per line in a fenced code block.", n=3, temperature=1.0)  # fmt: skip
    pool = [line.strip().rstrip(";") for r in replies for line in formalkit.extract_code(r).splitlines() if line.strip()]

    def check(pairs):
        asserts = "\n    ".join(f'__CPROVER_assert({c}, "{label}");' for label, c in pairs)
        return cbmc.run(program.replace("/* CANDIDATES */", asserts))

    out = houdini(pool, check)
    show("houdini", f"pool={len(pool)} kept={out.kept} proved={out.proved} rounds={out.rounds}")


def run_library():
    """LEGO-Prover: grow a library of verified lemmas, reuse them by name in later proofs."""
    lean = formalkit.backend("lean")
    lib = formalkit.Library()
    for name, statement in [("two_mul_eq", "theorem two_mul_eq (n : ℕ) : n + n = 2 * n"),
                            ("sq_nonneg_nat", "theorem sq_nonneg_nat (n : ℕ) : 0 ≤ n * n")]:  # fmt: skip
        steps = formalkit.patterns.refine(llm, lean, f"Prove in Lean 4 (no imports needed):\n{statement}")
        lib.add(name, steps[-1].arguments["code"], steps[-1].result)
    later = formalkit.patterns.refine(llm, lib.attach(lean), "Prove: theorem t (k : ℕ) : k + k + 0 = 2 * k",
                                      context=lib.context())  # fmt: skip
    show("library", f"proved lemmas={[e.name for e in lib.proved()]}  later proof: {later[-1].result.verdict}")


RUNS = {"decompose": run_decompose, "repair": run_repair, "route": run_route, "instantiate": run_instantiate,
        "soft": run_soft, "houdini": run_houdini, "library": run_library}  # fmt: skip

if __name__ == "__main__":
    for name in sys.argv[1:] or RUNS:
        RUNS[name]()
