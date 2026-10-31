"""Every integration pattern, end to end, with a real model.

    OPENAI_BASE_URL=https://api.deepseek.com OPENAI_API_KEY=... MODEL=deepseek-flash \\
        python examples/patterns.py [refine vote agent pot cegis geometry formalize sketch search]
"""

import os
import sys
from pathlib import Path

from openai import OpenAI

import formalkit
from formalkit.patterns import (
    ask_with_feedback,
    cegis,
    formalize,
    llm_close,
    llm_steps,
    propose_until_proved,
    refine,
    sample,
    sketch_and_fill,
    step_search,
    vote,
)

EXAMPLES = Path(__file__).parent
llm = formalkit.LLM(OpenAI(), os.environ.get("MODEL", "gpt-5"), max_tokens=8192)
PUZZLE = (
    "Alice, Bob and Carol each own exactly one of a cat, a dog and a fish (all different). "
    "Alice is allergic to fur, so she owns neither the cat nor the dog. Bob does not own the dog. "
    "Prove that Carol owns the dog."
)


def show(title, value):
    print(f"\n=== {title}\n{value}")


def run_refine():
    """Translate-and-solve with solver-driven self-refinement (Logic-LM)."""
    steps = refine(llm, formalkit.backend("z3"), PUZZLE + " Assert the negation of the claim last.")
    show("refine", [str(s.result.verdict) for s in steps])


def run_vote():
    """Several independent formalizations; agreement decides (self-consistency)."""
    steps = sample(llm, formalkit.backend("z3"), PUZZLE + " Assert the negation of the claim last.", n=3)
    result = vote(steps)
    show("vote", f"{result.winner} with {len(result.support)} of {len(steps)} ({result.counts})")


def run_agent():
    """The agentic loop, with the non-vacuity evidence policy and cited evidence."""
    agent = formalkit.Agent(llm, backends=["z3", "clingo"], evidence=formalkit.nonvacuous())
    answer = agent.solve(
        "What is the minimum number of colors needed to properly color the vertices of a 5-cycle? "
        "Establish both that it is achievable and that one fewer is impossible."
    )
    show("agent", f"{answer}  verified={answer.verified}  recheck={answer.recheck()}")


def run_pot():
    """Proof of Thought's JSON DSL as an intermediate representation."""
    answer = formalkit.Agent(llm, backends=["pot"]).solve(PUZZLE)
    show("pot", f"{answer}  compiled lines={len(answer.evidence[0].result.details['compiled'].splitlines()) if answer.evidence else 0}")


def run_cegis():
    """CEGIS: the model proposes plans, VAL refutes them with the failing step."""
    domain = (EXAMPLES / "downward/sat-blocks.pddl").read_text()
    problem = (EXAMPLES / "downward/sat-blocks.problem.pddl").read_text()
    downward = formalkit.backend("downward")
    task = (
        "Write a plan for this PDDL planning problem: one action per line, like (pick-up a).\n\n"
        f"Domain:\n{domain}\n\nProblem:\n{problem}"
    )
    loop = cegis(ask_with_feedback(llm, task), lambda plan: downward.run(domain, problem=problem, plan=plan), rounds=5)
    show("cegis", f"ok={loop.ok} after {len(loop.steps)} candidate(s): {[str(s.result.verdict) for s in loop.steps]}")


def run_geometry():
    """AlphaGeometry-style: the model adds auxiliary points, DD+AR does all deduction."""
    problem = "a b c = triangle a b c; d = on_tline d b a c, on_tline d c a b ? perp a d b c"
    ddar = formalkit.backend("ddar")
    task = (
        "This AlphaGeometry problem saturates without a proof. Add ONE auxiliary construction "
        "(a new point defined with the same construction language, e.g. `e = on_line e a c, on_line e b d`) "
        f"before the `?` and return the whole problem on one line.\n\nProblem:\n{problem}\n\n"
        f"Construction language reference:\n{ddar.spec.guidance}"
    )
    loop = propose_until_proved(ddar, problem, ask_with_feedback(llm, task), rounds=4)
    show("geometry", f"ok={loop.ok}: {loop.candidate}")


def run_formalize_and_sketch():
    """Autoformalize a statement, then let automation close the hole (DSP)."""
    lean = formalkit.backend("lean")
    step = formalize(llm, lean, "For every natural number n, n * (n + 1) is even.", timeout=120)
    show("formalize", f"{step.result.verdict}\n{step.arguments['code']}")
    filled = sketch_and_fill(lean, step.arguments["code"], close=llm_close(llm))  # automation first, then the model
    show("sketch_and_fill", f"proved={filled.proved} fills={filled.fills}\n{filled.code}")


def run_search():
    """GPT-f-style best-first search over Lean proof states, the model proposing tactics."""
    lean = formalkit.backend("lean")
    root = lean.start("import Mathlib\n\ntheorem t (a b : ℕ) (h : a ≤ b) : a * a ≤ b * b := by\n  sorry", timeout=120)
    search = step_search(root, llm_steps(llm, n=4), budget=12)
    show("step_search", f"solved={search.solved is not None} expanded={search.expanded} tried={search.tried}\n"
                        f"{search.proof or ''}")


RUNS = {
    "refine": run_refine, "vote": run_vote, "agent": run_agent, "pot": run_pot, "cegis": run_cegis,
    "geometry": run_geometry, "formalize": run_formalize_and_sketch, "search": run_search,
}  # fmt: skip

if __name__ == "__main__":
    for name in sys.argv[1:] or RUNS:
        RUNS[name]()
