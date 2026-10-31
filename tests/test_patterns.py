"""The patterns, with scripted LLMs and toy backends (no Docker)."""

from __future__ import annotations

import re

import pytest
from conftest import Countdown, Fixed, ScriptedClient

from formalkit import LLM, Result, Verdict
from formalkit.agent import Step
from formalkit.patterns import (
    ask_with_feedback,
    cegis,
    formalize,
    holes,
    llm_close,
    llm_steps,
    propose_until_proved,
    refine,
    sample,
    sketch_and_fill,
    step_search,
    translate_and_solve,
    vote,
)


def fenced(text):
    return (f"Here you go:\n```\n{text}\n```", None)


# -- refine / translate / formalize ------------------------------------------------------


def test_refine_feeds_errors_back_until_decisive():
    b = Fixed("b", lambda code: (Verdict.UNSAT,) if code == "good" else (Verdict.ERROR, "line 1: bad token"))
    client = ScriptedClient([fenced("bad"), fenced("good")])
    steps = refine(LLM(client, "m"), b, "problem", rounds=3)
    assert [s.result.verdict for s in steps] == [Verdict.ERROR, Verdict.UNSAT]
    assert "line 1: bad token" in client.seen[1]["messages"][-1]["content"]
    assert steps[-1].ref is b


def test_translate_and_solve_is_one_shot():
    b = Fixed("b", lambda code: (Verdict.ERROR,))
    step = translate_and_solve(LLM(ScriptedClient([fenced("x")]), "m"), b, "problem")
    assert step.result.verdict is Verdict.ERROR and b.runs == ["x"]


def test_formalize_stops_once_the_statement_elaborates():
    b = Fixed("lean", lambda code: (Verdict.UNKNOWN,) if "sorry" in code else (Verdict.ERROR,))
    client = ScriptedClient([fenced("theorem t : 1 = 1 := by rfl ???"), fenced("theorem t : 1 = 1 := by sorry")])
    step = formalize(LLM(client, "m"), b, "one equals one")
    assert step.arguments["code"].endswith("sorry") and step.result.verdict is Verdict.UNKNOWN
    assert "leave the proof as `sorry`" in client.seen[0]["messages"][1]["content"]


# -- sketch and fill -----------------------------------------------------------------------


def test_holes_ignore_comments_and_identifiers():
    code = "a := by sorry -- sorry\n/- sorry -/ b := sorry\nsorry_lemma\nx.sorry"
    assert len(holes(code)) == 2


def _prover(code):
    """'sorry' left -> unknown; a hole filled with 'bad' -> error; else proved."""
    if "bad" in code:
        return (Verdict.ERROR,)
    return (Verdict.UNKNOWN, code, {"goals": ["g1", "g2"]}) if holes(code) else (Verdict.PROVED,)


def test_sketch_and_fill_closes_holes_in_order():
    b = Fixed("toyprover", _prover)
    sketch = "have h1 := by sorry\nhave h2 :=\n  sorry\ndone"
    filled = sketch_and_fill(b, sketch, closers=["bad", "auto"], close=lambda goal: [f"exact {goal}"])
    assert filled.proved and filled.fills == ["auto", "auto"]
    assert filled.code == "have h1 := by auto\nhave h2 :=\n  auto\ndone"


def test_sketch_and_fill_uses_model_closers_and_rejects_smuggled_holes():
    b = Fixed("toyprover", lambda code: (Verdict.ERROR,) if "auto" in code else _prover(code))
    filled = sketch_and_fill(b, "x := sorry", closers=["auto", "sorry"], close=lambda g: ["first\nsecond"])
    assert filled.proved and filled.fills == ["first\nsecond"]
    assert "first" in filled.code and "second" in filled.code and "sorry" not in filled.code


def test_sketch_and_fill_reports_unclosed_holes():
    b = Fixed("toyprover", _prover)
    filled = sketch_and_fill(b, "a := sorry\nb := sorry", closers=["bad"])
    assert not filled.proved and filled.fills == [None, None] and filled.result.verdict is Verdict.UNKNOWN


def test_sketch_and_fill_passes_goals_to_close():
    b = Fixed("toyprover", _prover)
    asked = []
    sketch_and_fill(b, "a := sorry\nb := sorry", closers=[], close=lambda g: asked.append(g) or ["ok"])
    assert asked == ["g1", "g2"]


# -- step search ----------------------------------------------------------------------------


def test_step_search_finds_a_proof_and_branches():
    backend = Countdown()
    root = backend.start("7")
    result = step_search(root, lambda s: ["9", "3", "2"], budget=10)  # "9" always fails
    path = result.solved.path
    assert sum(map(int, path)) == 7 and len(path) == 3 and set(path) <= {"3", "2"}  # shallowest proof
    assert result.solved.proof == "steps"


def test_step_search_respects_budget_and_dedupes():
    backend = Countdown()
    result = step_search(backend.start("100"), lambda s: ["1"], budget=5)
    assert result.solved is None and result.expanded == 5 and result.tried == 5


def test_state_is_immutable_and_branchable():
    backend = Countdown()
    root = backend.start("5")
    a, b = root.apply("2"), root.apply("3")
    assert a.goals == ["reach 0 from 3"] and b.goals == ["reach 0 from 2"] and root.goals == ["reach 0 from 5"]
    assert root.apply("9").failed
    with pytest.raises(ValueError):
        b.apply("2").apply("1")


def test_llm_steps_parses_candidates():
    client = ScriptedClient([fenced("3\n\n2\n1\n1")])
    propose = llm_steps(LLM(client, "m"), n=3)
    assert propose(Countdown().start("4")) == ["3", "2", "1"]
    assert "reach 0 from 4" in client.seen[0]["messages"][0]["content"]


# -- CEGIS / propose-until-proved ----------------------------------------------------------


def test_cegis_learns_from_counterexamples():
    def verify(n):
        n = int(n)
        if n * n >= 50:
            return Result(Verdict.PROVED, "ok", backend="checker")
        return Result(Verdict.REFUTED, f"{n}^2 < 50", {"counterexample": n}, "checker")

    def propose(history):
        return 1 if not history else history[-1].result.counterexample * 2

    loop = cegis(propose, verify, rounds=10)
    assert loop.ok and loop.candidate == 8 and [s.result.counterexample for s in loop.steps[:-1]] == [1, 2, 4]


def test_cegis_gives_up():
    loop = cegis(lambda h: "x", lambda c: Result(Verdict.REFUTED), rounds=3)
    assert not loop.ok and len(loop.steps) == 3


def test_propose_until_proved_adds_constructions():
    engine = Fixed("ddar", lambda code: (Verdict.PROVED,) if "aux" in code else (Verdict.UNKNOWN, "saturated"))
    loop = propose_until_proved(engine, "problem ? goal", lambda history: history[-1].arguments["code"].replace("?", "aux ?"))
    assert loop.ok and loop.candidate == "problem aux ? goal" and [s.result.verdict for s in loop.steps] == [
        Verdict.UNKNOWN, Verdict.PROVED]  # fmt: skip


def test_propose_until_proved_stops_on_refutation():
    engine = Fixed("ddar", lambda code: (Verdict.REFUTED,))
    loop = propose_until_proved(engine, "p", lambda h: "never")
    assert not loop.ok and len(loop.steps) == 1


def test_ask_with_feedback_shows_history():
    client = ScriptedClient([fenced("v2")])
    history = [Step("b", {"code": "v1"}, Result(Verdict.REFUTED, "fails at step 3"))]
    assert ask_with_feedback(LLM(client, "m"), "Make a plan.")(history) == "v2"
    prompt = client.seen[0]["messages"][-1]["content"]
    assert "Make a plan." in prompt and "v1" in prompt and "fails at step 3" in prompt


# -- vote / sample ---------------------------------------------------------------------------


def _s(verdict):
    return Step("b", {"code": ""}, Result(verdict))


def test_vote():
    v = vote([_s(Verdict.UNSAT), _s(Verdict.SAT), _s(Verdict.UNSAT), _s(Verdict.ERROR)])
    assert v.winner is Verdict.UNSAT and len(v.support) == 2 and v.counts == {Verdict.UNSAT: 2, Verdict.SAT: 1}
    assert vote([_s(Verdict.UNSAT), _s(Verdict.SAT)]).winner is None
    assert vote([_s(Verdict.ERROR)]).winner is None


def test_sample_runs_independent_formalizations():
    b = Fixed("b", lambda code: (Verdict.SAT,) if "a" in code else (Verdict.UNSAT,))
    client = ScriptedClient([fenced("a"), fenced("b"), fenced("a")])
    steps = sample(LLM(client, "m"), b, "problem", n=3, temperature=1.0)
    assert len(steps) == 3 and all(s["temperature"] == 1.0 for s in client.seen)
    assert vote(steps).winner is Verdict.SAT
    assert re.search("problem", client.seen[0]["messages"][1]["content"])


def test_llm_close_returns_one_candidate_per_block():
    client = ScriptedClient([("Option 1:\n```lean\nsimp\n```\nOption 2:\n```lean\ninduction n with\n| zero => rfl\n| succ => simp\n```", None)])
    close = llm_close(LLM(client, "m"), n=3)
    assert close("⊢ P") == ["simp", "induction n with\n| zero => rfl\n| succ => simp"]
    assert "⊢ P" in client.seen[0]["messages"][-1]["content"]
