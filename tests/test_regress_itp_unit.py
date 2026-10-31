"""Regressions in the proof patterns' text handling (no Docker)."""

from __future__ import annotations

import pytest
from conftest import Fixed

from formalkit import Verdict
from formalkit.patterns import holes, sketch_and_fill
from formalkit.patterns.prove import _fill


@pytest.mark.parametrize(
    "code,count",
    [
        ('def s := "sorry"\ntheorem t : P := by\n  sorry', 1),  # strings are not holes
        ('def s := "a \\" sorry"\ntheorem t : P := sorry', 1),  # escaped quotes
        ("/- outer /- nested sorry -/ still a comment sorry -/\ntheorem t : P := sorry", 1),  # nested comments
        ("-- sorry\ntheorem t : P := sorry -- sorry", 1),
        ('text \\<open>sorry \\<open>nested sorry\\<close>\\<close>\nlemma "x" sorry', 1),  # Isabelle cartouches
        ("(* sorry *) lemma \"x\" sorry", 1),
        ("theorem sorry_free : P := my_sorry_lemma", 0),
    ],
)
def test_holes_ignore_non_code(code, count):
    assert len(holes(code)) == count


@pytest.mark.parametrize(
    "code,text,expected",
    [
        ("theorem t : P := sorry", "simp", "theorem t : P := (by simp)"),  # term position
        ("  have h : x := sorry", "omega", "  have h : x := (by omega)"),
        ("exact ⟨hp, sorry⟩", "simp", "exact ⟨hp, (by simp)⟩"),
        ("theorem t : P := sorry", "by simp", "theorem t : P := by simp"),  # already a term
        ("theorem t : P := by\n  sorry", "simp", "theorem t : P := by\n  simp"),  # tactic position
        ("theorem t : P := by\n  sorry", "intro x\nsimp", "theorem t : P := by\n  intro x\n  simp"),
        ('lemma "x" sorry', "by auto", 'lemma "x" by auto'),  # Isabelle proof command
        ("x := sorry", "a\nb", "x := (by\n       a\n       b)"),  # multi-line term: an indented by-block
    ],
)
def test_fill_respects_hole_position(code, text, expected):
    assert _fill(code, holes(code)[0], "sorry", text) == expected


def test_sketch_and_fill_handles_term_holes():
    # A toy checker that only accepts the term-position fill a real Lean would accept.
    def lean_like(code):
        if holes(code):
            return (Verdict.UNKNOWN,)
        return (Verdict.PROVED,) if code.endswith(":= (by simp)") else (Verdict.ERROR,)

    lean_like = Fixed("toy", lean_like)
    filled = sketch_and_fill(lean_like, "theorem t : P := sorry", closers=["simp"])
    assert filled.proved and filled.code == "theorem t : P := (by simp)"


def test_llm_steps_strips_list_markers_and_backticks():
    from conftest import Countdown, ScriptedClient

    from formalkit import LLM
    from formalkit.patterns import llm_steps

    reply = "Candidates:\n```\n1. simp\n2) `omega`\n- nlinarith [sq_nonneg a]\n· rfl\n1. simp\n```"
    propose = llm_steps(LLM(ScriptedClient([(reply, None)]), "m"), n=5)
    assert propose(Countdown().start("3")) == ["simp", "omega", "nlinarith [sq_nonneg a]", "· rfl"]


def test_llm_close_without_fences_uses_the_reply():
    from conftest import ScriptedClient

    from formalkit import LLM
    from formalkit.patterns import llm_close

    assert llm_close(LLM(ScriptedClient([("  omega  ", None)]), "m"))("⊢ P") == ["omega"]
    assert llm_close(LLM(ScriptedClient([("   ", None), ("", None)]), "m"))("⊢ P") == []  # empty twice: nothing


def test_sketch_and_fill_tries_file_level_indentation():
    # The model wrote the fill at the file's indentation: continuation lines already carry the hole's column.
    sketch = "theorem t : P := by\n  sorry"
    fill = "rw [foo]\n  have h : P := by\n    omega\n  exact h"
    good = "theorem t : P := by\n  rw [foo]\n  have h : P := by\n    omega\n  exact h"

    def checker(code):
        if holes(code):
            return (Verdict.UNKNOWN,)
        return (Verdict.PROVED,) if code == good else (Verdict.ERROR,)  # over-indented: rejected

    filled = sketch_and_fill(Fixed("toy", checker), sketch, closers=[], close=lambda goal: [fill])
    assert filled.proved and filled.code == good and filled.fills == [fill]


def test_decompose_tries_file_level_indentation():
    from conftest import ScriptedClient

    from formalkit import LLM
    from formalkit.patterns import decompose

    sketch_reply = "```\nhave h : X := by sorry\n  exact h\n```"  # continuation at the file's indentation
    good_prefix = "theorem t := by\n  have h : X := by"

    def checker(code):
        if "  exact h" in code and "    exact h" in code:
            return (Verdict.ERROR,)  # over-indented reading
        if holes(code):
            return (Verdict.UNKNOWN, code, {"goals": ["X" if "have h" in code else "top"] * len(holes(code))})
        return (Verdict.PROVED,) if code.startswith(good_prefix) else (Verdict.ERROR,)

    def reply(kwargs):
        prompt = kwargs["messages"][-1]["content"]
        if "too hard" in prompt:
            return (sketch_reply, None)
        return ("```\nbad\n```", None) if "Goal:\ntop" in prompt else ("```\nsimp\n```", None)

    calls = ScriptedClient([reply] * 30)
    out = decompose(LLM(calls, "m"), Fixed("toy", checker), "theorem t := by\n  sorry", depth=1, width=1)
    assert out.proved and "  exact h" in out.code and "    exact h" not in out.code


@pytest.mark.parametrize(
    "line,alt,expected",
    [
        ("  by simp", "by auto", "  by auto"),  # Isabelle: the alternative brings its own `by`
        ("theorem t : P := by bad", "simp", "theorem t : P := by simp"),  # Lean inline
        ("theorem t : P := by bad", "by simp", "theorem t : P := by simp"),
        ("  bad_tactic", "omega", "  omega"),
        ('lemma "x" by simp', "by auto", 'lemma "x" by auto'),
    ],
)
def test_tactic_swap_keeps_one_by(line, alt, expected):
    from formalkit import Result
    from formalkit.patterns import tactic_swap

    result = Result(Verdict.ERROR, "", {"messages": [{"severity": "error", "line": 1, "message": "x"}]})
    assert tactic_swap([alt])(line, result) == [expected]


def test_sketch_and_fill_gives_context_when_no_goal_is_reported():
    asked = []
    toy = Fixed("toy", lambda code: (Verdict.UNKNOWN,) if holes(code) else (Verdict.PROVED,))  # reports no goals
    sketch_and_fill(toy, 'lemma "x = x"\n  sorry', closers=[], close=lambda g: asked.append(g) or ["by simp"])
    assert "⟪HOLE⟫" in asked[0] and 'lemma "x = x"' in asked[0]


def test_sketch_and_fill_drops_a_duplicate_by():
    good = "theorem t : P := by\n  simp"
    def checker(code):
        if holes(code):
            return (Verdict.UNKNOWN,)
        return (Verdict.PROVED,) if code == good else (Verdict.ERROR,)

    toy = Fixed("toy", checker)
    filled = sketch_and_fill(toy, "theorem t : P := by\n  sorry", closers=[], close=lambda g: ["by simp"])
    assert filled.proved and filled.code == good


def test_step_search_survives_a_proposer_that_raises_once():
    from conftest import Countdown

    from formalkit.patterns import step_search

    calls = []

    def flaky(state):
        calls.append(state)
        if len(calls) == 1:
            raise ConnectionError("transient API error")
        return ["3", "2"]

    # The root's proposal fails; search continues once a state is re-expanded via a sibling proposer.
    from formalkit.patterns import mix

    result = step_search(Countdown().start("5"), mix(flaky, lambda s: ["2", "3"]), budget=10)
    assert result.solved is not None


def test_sketch_and_fill_survives_a_failing_closer():
    def close(goal):
        raise TimeoutError("model timed out")

    toy = Fixed("toy", lambda code: (Verdict.UNKNOWN,) if holes(code) else (Verdict.PROVED,))
    filled = sketch_and_fill(toy, "a := by\n  sorry", closers=["simp"], close=close)
    assert filled.proved and filled.fills == ["simp"]


def test_budget_exceeded_still_stops_patterns():
    from conftest import Countdown

    from formalkit import BudgetExceeded
    from formalkit.patterns import step_search

    def spent(state):
        raise BudgetExceeded("budget exceeded: tokens")

    with pytest.raises(BudgetExceeded):
        step_search(Countdown().start("5"), spent, budget=10)


def test_repair_keeps_attempts_when_the_model_fails():
    from formalkit import LLM
    from formalkit.patterns import repair

    class Down:
        class chat:  # noqa: N801
            class completions:  # noqa: N801
                @staticmethod
                def create(**kw):
                    raise ConnectionError("API down")

    toy = Fixed("toy", lambda code: (Verdict.ERROR,))
    steps = repair(toy, "broken", llm=LLM(Down(), "m"), rounds=3)
    assert len(steps) == 1 and steps[0].result.verdict is Verdict.ERROR


def test_step_search_with_only_a_failing_proposer_returns_unsolved():
    from conftest import Countdown

    from formalkit.patterns import step_search

    def down(state):
        raise ConnectionError("API down")

    result = step_search(Countdown().start("5"), down, budget=3)
    assert result.solved is None and result.tried == 0


def test_sketch_and_fill_rejects_disguised_holes():
    def checker(code):
        if holes(code) or "admit" in code or "oops" in code:
            return (Verdict.UNKNOWN,)
        return (Verdict.PROVED,) if "real" in code else (Verdict.ERROR,)

    filled = sketch_and_fill(Fixed("toy", checker), "a := by\n  sorry", closers=["admit", "oops", "real"])
    assert filled.proved and filled.fills == ["real"]


def test_last_hole_needs_a_proof():
    # A checker that stays UNKNOWN for a fill (e.g. it left a goal open somewhere): not a fill of the last hole.
    checker = Fixed("toy", lambda code: (Verdict.UNKNOWN,))
    filled = sketch_and_fill(checker, "a := by\n  sorry", closers=["simp"])
    assert filled.fills == [None] and not filled.proved


def test_sketch_and_fill_does_not_wait_for_slow_candidates():
    import time

    def checker(code):
        if holes(code):
            return (Verdict.UNKNOWN,)
        if "slow" in code:
            time.sleep(8)  # e.g. aesop grinding to the timeout
            return (Verdict.ERROR,)
        return (Verdict.PROVED,) if "fast" in code else (Verdict.ERROR,)

    start = time.monotonic()
    filled = sketch_and_fill(Fixed("toy", checker), "a := by\n  sorry", closers=["slow", "fast"])
    assert filled.proved and filled.fills == ["fast"] and time.monotonic() - start < 5


@pytest.mark.parametrize(
    "code,count",
    [
        ("def q : Char := '\"'\ntheorem u : 1 = 1 := by\n  sorry", 1),  # '"' is a char, not a string opener
        ("def b := '\\''\ntheorem t : P := sorry", 1),
        ("theorem h' : x' = x' := rfl -- sorry", 0),  # primes in names are not char literals
    ],
)
def test_holes_after_char_literals(code, count):
    assert len(holes(code)) == count


def test_lean_guards_see_past_char_literals():
    from formalkit.adapters import lean as L

    code = "def q : Char := '\"'\n#eval 1\nexample : 2 ^ 10 = 1024 := by native_decide"
    masked = L._mask(code)
    assert L._NATIVE_RE.search(masked) and L._EXEC_RE.search(masked)


def test_proposers_retry_an_empty_reply():
    # A reasoning model that spent its whole budget thinking returns empty content.
    from conftest import ScriptedClient

    from formalkit import LLM
    from formalkit.patterns import llm_close

    client = ScriptedClient([("", None), ("```\nsimp\n```", None)])
    assert llm_close(LLM(client, "m"))("⊢ P") == ["simp"] and len(client.seen) == 2
