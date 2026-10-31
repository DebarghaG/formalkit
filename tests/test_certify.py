"""Final certification of Lean proofs with Lake's own judges (`lake comparator`, `lake check`)."""

from __future__ import annotations

import pytest

from formalkit import Verdict, backend, docker
from formalkit.patterns import pinned

pytestmark = pytest.mark.docker

CHALLENGE = "import Mathlib\n\ntheorem t (x : ℝ) : 0 ≤ x ^ 2 := by\n  sorry\n"


@pytest.fixture(scope="module")
def lean():
    if not docker.has_image("lean"):
        pytest.skip("lean image not built")
    b = backend("lean")
    if "challenge" not in b.spec.inputs:
        pytest.skip("lean image predates certification")
    return b


def test_a_proof_of_the_challenge_is_certified(lean):
    solution = "import Mathlib\n\ntheorem helper (x : ℝ) : 0 ≤ x ^ 2 := by positivity\ntheorem t (x : ℝ) : 0 ≤ x ^ 2 := helper x\n"
    r = lean.run(solution, timeout=300, challenge=CHALLENGE)
    assert r.verdict is Verdict.PROVED, r.feedback()
    cert = r.details["certified"]
    assert cert["tool"] == "lake comparator" and cert["theorems"] == ["t"] and cert["permitted_axioms"] == [
        "propext", "Quot.sound", "Classical.choice"]  # fmt: skip


def test_proving_a_different_statement_is_rejected(lean):
    solution = "import Mathlib\n\ntheorem t (x : ℝ) : 0 ≤ x ^ 2 + 0 := by positivity\n"
    assert lean.run(solution, timeout=300).verdict is Verdict.PROVED  # a fine proof - of something else
    r = lean.run(solution, timeout=300, challenge=CHALLENGE)
    assert r.verdict is Verdict.ERROR and "do not match" in r.output and r.details["certified"] is False


def test_a_free_form_proof_keeps_the_fast_audit(lean):
    r = lean.run("theorem u (n : Nat) : n + 0 = n := by simp\n", timeout=120)
    assert r.verdict is Verdict.PROVED and "certified" not in r.details  # no challenge: kernel replay + axiom audit


def test_the_pinned_backend_certifies_against_its_statement(lean):
    r = pinned(lean, CHALLENGE).run("positivity", timeout=300)
    assert r.verdict is Verdict.PROVED and r.details["certified"]["tool"] == "lake comparator"


def test_a_solved_session_is_certified_against_its_starting_file(lean):
    root = lean.start("theorem s (a b : Nat) : a + b = b + a := by\n  sorry", timeout=120)
    done = root.apply("omega", timeout=300)
    assert done.solved and done.result.details["certified"]["theorems"] == ["s"]


def test_definition_holes_are_flagged_for_review(lean):
    challenge = "def big : Nat := sorry\n\ntheorem big_gt : 37 < big := sorry\n"
    solution = "def big : Nat := 100\n\ntheorem big_gt : 37 < big := by decide\n"
    r = lean.run(solution, timeout=300, challenge=challenge)
    assert r.verdict is Verdict.PROVED and r.details["needs_review"] == ["big"]
