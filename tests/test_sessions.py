"""Step-by-step sessions (Lean REPL) and structured goals (Lean, Isabelle).

Needs the lean and isabelle images:  pytest -m docker -k sessions
"""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

from formalkit import Verdict, backend, docker

pytestmark = pytest.mark.docker
EXAMPLES = Path(__file__).resolve().parent.parent / "examples"


def _has_repl() -> bool:
    if not docker.has_image("lean"):
        return False
    probe = subprocess.run(
        ["docker", "run", "--rm", "--entrypoint", "sh", docker.image("lean"), "-c", "test -x \"$LEAN_REPL\""],
        capture_output=True,
    )
    return probe.returncode == 0


@pytest.fixture(scope="module")
def lean():
    if not _has_repl():
        pytest.skip("lean image with the REPL not built")
    return backend("lean")


@pytest.fixture(scope="module")
def isabelle():
    if not docker.has_image("isabelle"):
        pytest.skip("isabelle image not built")
    return backend("isabelle")


CONJ = "theorem t (n : Nat) (h : 0 < n) : n + 0 = n ∧ True := by sorry"


def test_start_reports_the_goal(lean):
    root = lean.start(CONJ)
    assert root.result.verdict is Verdict.UNKNOWN and root.id
    assert root.goals == ["n : Nat\nh : 0 < n\n⊢ n + 0 = n ∧ True"]


def test_failing_step_is_a_failed_state(lean):
    bad = lean.start(CONJ).apply("exact foo")
    assert bad.failed and bad.id is None and "foo" in bad.result.output
    with pytest.raises(ValueError):
        bad.apply("simp")


def test_states_branch(lean):
    root = lean.start(CONJ)
    a, b = root.apply("constructor"), root.apply("constructor")
    assert a.id != b.id and a.goals == b.goals and len(a.goals) == 2
    assert root.apply("exact ⟨rfl, trivial⟩").solved  # root is still usable


def test_multi_step_proof_is_kernel_checked(lean):
    s = lean.start(CONJ).apply("constructor")
    s = s.apply("· induction n with\n  | zero => simp\n  | succ k ih => simp")
    assert s.goals == ["case right\nn : Nat\nh : 0 < n\n⊢ True"]
    done = s.apply("· trivial")
    assert done.solved and done.id is None and done.path == ("constructor", s.path[-1], "· trivial")
    assert lean.run(done.proof).verdict is Verdict.PROVED


@pytest.mark.parametrize(
    "code",
    [
        "theorem u (a b : Nat) : a + b = b + a := by sorry",  # inline after `by`
        "theorem u (a b : Nat) : a + b = b + a := by\n  sorry",  # own line in a tactic block
        "theorem u (a b : Nat) : a + b = b + a :=\n  sorry",  # term position
        "theorem u (a b : Nat) : True ∧ a + b = b + a := by\n  constructor\n  · trivial\n  · sorry",  # after a bullet
        "theorem u (a b : Nat) : True ∧ a + b = b + a := ⟨trivial, sorry⟩",  # inside a term
    ],
)
def test_hole_positions_assemble(lean, code):
    done = lean.start(code).apply("omega")
    assert done.solved, done.result.output
    assert lean.run(done.proof).verdict is Verdict.PROVED


def test_mathlib_session(lean):
    root = lean.start("import Mathlib\n\ntheorem w (x : ℝ) (h : 0 < x) : 0 < x ^ 2 + x := by sorry", timeout=180)
    assert root.goals == ["x : ℝ\nh : 0 < x\n⊢ 0 < x ^ 2 + x"]
    assert root.apply("positivity", timeout=120).solved


@pytest.mark.parametrize("code", ["theorem z : 1 = 1 := rfl", "theorem z : 1 = 1 := sorry\ntheorem y : 2 = 2 := sorry"])
def test_start_needs_exactly_one_hole(lean, code):
    root = lean.start(code)
    assert root.failed and "exactly one `sorry`" in root.result.output


def test_sorry_in_comments_is_not_a_hole(lean):
    root = lean.start("-- sorry\n/- sorry -/\ntheorem z : 1 = 1 := by sorry")
    assert root.goals == ["⊢ 1 = 1"]


def test_cheating_path_is_not_proved(lean):
    for cheat in ("sorry", "admit"):
        end = lean.start(CONJ).apply(cheat)
        assert not end.solved and end.result.verdict is Verdict.UNKNOWN


def test_unknown_state_is_an_error(lean):
    assert lean._step("no-such-state", "simp", 10).verdict is Verdict.ERROR


def test_run_reports_goals(lean):
    sorry = lean.run((EXAMPLES / "lean/unknown-sorry.lean").read_text())
    assert sorry.verdict is Verdict.UNKNOWN and sorry.goals == ["n : Nat\nh : n > 2\n⊢ n * n > 2 * n"]
    unsolved = lean.run((EXAMPLES / "lean/error-unsolved-goal.lean").read_text())
    assert unsolved.verdict is Verdict.ERROR and unsolved.goals and "⊢ n + 1 + b = b + (n + 1)" in unsolved.goals[0]


def test_isabelle_reports_goals(isabelle):
    r = isabelle.run((EXAMPLES / "isabelle/error-unfinished.thy").read_text())
    assert r.verdict is Verdict.ERROR and r.goals == ["xs = []"]
