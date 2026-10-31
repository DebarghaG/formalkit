"""Observers, library, premises and the §4/§5 patterns, with toys and scripted models (no Docker)."""

from __future__ import annotations

import json

import pytest
from conftest import Countdown, Fixed, ScriptedClient

from formalkit import LLM, Budget, BudgetExceeded, Library, Result, Trace, Verdict, observe, premises
from formalkit.agent import Step
from formalkit.learn import (
    Curriculum,
    binary,
    compiles,
    evaluate,
    expert_iteration,
    prefix_labels,
    repair_pairs,
    rollouts,
    to_rl_rows,
    write_jsonl,
)
from formalkit.patterns import (
    assume_and_discharge,
    automation,
    backtranslate,
    best_of,
    conjecture,
    cycle_consistency,
    decompose,
    holes,
    houdini,
    label,
    localize,
    mix,
    probe,
    repair,
    route,
    step_search,
    suggest,
    tactic_swap,
)


def fenced(text):
    return (f"```\n{text}\n```", None)


# -- observers ---------------------------------------------------------------------------


def test_trace_records_runs_steps_and_llm_calls():
    trace = Trace()
    b = Countdown()
    with observe(trace):
        root = b.start("3")
        root.apply("9")  # error
        root.apply("1")  # progress
        root.apply("3")  # solved
        LLM(ScriptedClient([("hi", None)]), "m").ask("q")
    root.apply("2")  # outside the block: not recorded
    assert [e.kind for e in trace.events] == ["start", "step", "step", "step", "llm"]
    assert [t["outcome"] for t in trace.tactics()] == ["error", "progress", "solved"]
    assert trace.tactics()[1] == {"goals": ["reach 0 from 3"], "tactic": "1", "outcome": "progress",
                                  "next_goals": ["reach 0 from 2"]}  # fmt: skip
    assert trace.preferences() == [{"goals": ["reach 0 from 3"], "chosen": "3", "rejected": "9"}]
    assert trace.proofs() == [{"backend": "countdown", "input": "3", "proof": "steps"}]


def test_budget_stops_work():
    b = Fixed("b", lambda code: (Verdict.UNKNOWN,))
    budget = Budget(calls=3)
    with pytest.raises(BudgetExceeded, match="calls"), observe(budget):
        for _ in range(10):
            b.run("x")
    assert budget.spent["calls"] == 4 and len(b.runs) == 4


def test_budget_counts_tokens():
    with pytest.raises(BudgetExceeded, match="tokens"), observe(Budget(tokens=25)):
        llm = LLM(ScriptedClient([("a", None)] * 5), "m")
        for _ in range(5):
            llm.ask("q")  # 10 tokens each


# -- library -------------------------------------------------------------------------------


def test_library_admits_by_authority_and_retrieves():
    lib = Library()
    lib.add("add_zero", "theorem add_zero (n : Nat) : n + 0 = n := rfl", Result(Verdict.PROVED, backend="lean"))
    lib.add("bogus", "theorem bogus : 1 = 2 := sorry", Result(Verdict.UNKNOWN, backend="lean"))
    lib.add("add_zero", "theorem add_zero ... := sorry", Result(Verdict.UNKNOWN))  # never downgrades
    assert [e.name for e in lib.proved()] == ["add_zero"] and lib.entries["add_zero"].proved
    assert [e.name for e in lib.search("n + 0 = n")] == ["add_zero"]
    assert [e.name for e in lib.search("1 = 2", proved_only=False)][0] == "bogus"
    assert "add_zero" in lib.context()("n + 0") and lib.context()("zzz") == ""


def test_library_attach_hoists_imports(tmp_path):
    lib = Library()
    lib.add("l1", "import Mathlib\ntheorem l1 : True := trivial", Result(Verdict.PROVED))
    inner = Fixed("lean", lambda code: (Verdict.PROVED,))
    attached = lib.attach(inner)
    attached.run("import Mathlib.Tactic\ntheorem t : True := l1")
    sent = inner.runs[-1]
    assert sent.startswith("import Mathlib\nimport Mathlib.Tactic\n") and sent.index("theorem l1") < sent.index("theorem t")
    lib.save(tmp_path / "lib.jsonl")
    assert Library.load(tmp_path / "lib.jsonl").entries["l1"].proved


def test_premises_prepends_and_checks_consistency():
    seen = []
    smt = Fixed("smt", lambda code: (seen.append(code) or Verdict.SAT,), language="SMT-LIB 2.6")
    kb = premises(smt, "(declare-const x Int)\n(assert (> x 0))")
    kb.run("(assert (< x 0))\n(check-sat)")
    assert seen[-1].startswith("(declare-const x Int)") and seen[-1].endswith("(check-sat)")
    assert kb.consistent().verdict is Verdict.SAT and seen[-1].rstrip().endswith("(check-sat)")
    assert kb.spec.name == "smt_premises" and "(assert (> x 0))" in kb.spec.guidance


# -- generate ----------------------------------------------------------------------------------


def test_route_by_model_or_classifier():
    a, b = Fixed("clingo", lambda c: (Verdict.SAT,)), Fixed("z3", lambda c: (Verdict.SAT,))
    assert route(LLM(ScriptedClient([("I'd use z3.", None)]), "m"), "p", [a, b]) is b
    assert route(lambda problem, backends: backends[0], "p", [a, b]) is a


def test_backtranslate_and_cycle_consistency():
    client = ScriptedClient([("Every n plus zero is n.", None), ("Score: 9", None)])
    assert cycle_consistency(LLM(client, "m"), "n + 0 = n for all n", "theorem t (n : Nat) : n + 0 = n") == 0.9
    assert "theorem t" in client.seen[0]["messages"][-1]["content"]
    assert backtranslate(LLM(ScriptedClient([("  S. ", None)]), "m"), "x") == "S."


def test_conjecture_filters_invalid_and_trivial():
    lean = Fixed("lean", lambda code: (Verdict.ERROR,) if "bad" in code else (Verdict.UNKNOWN,))
    client = ScriptedClient([fenced("theorem a : P := sorry"), fenced("bad"), fenced("theorem b : Q := sorry")])
    out = conjecture(LLM(client, "m"), lean, "seed", n=3, trivial=lambda code: "a :" in code)
    assert [(c.valid, c.trivial) for c in out] == [(True, True), (False, False), (True, False)]


# -- prove ---------------------------------------------------------------------------------------


def _messages(*lines):
    return {"messages": [{"severity": "error", "line": n, "message": "boom"} for n in lines]}


def test_localize_and_tactic_swap():
    code = "theorem t : P := by\n  intro h\n  bad_tactic\n  done"
    result = Result(Verdict.ERROR, "boom", _messages(3))
    shown = localize(code, result)
    assert ">>   3 |   bad_tactic" in shown and "     1 | theorem" in shown
    fixes = tactic_swap(["simp", "omega"])(code, result)
    assert fixes[0] == "theorem t : P := by\n  intro h\n  simp\n  done"
    inline = tactic_swap(["simp"])("theorem t : P := by bad", Result(Verdict.ERROR, "", _messages(1)))
    assert inline == ["theorem t : P := by simp"]


def test_repair_tries_fixers_before_the_model():
    lean = Fixed("lean", lambda c: (Verdict.PROVED,) if "good" in c else (Verdict.ERROR, "e", _messages(2)))
    steps = repair(lean, "x\n  bad", fixers=[tactic_swap(["nope", "good"])], llm=None)
    assert [s.result.verdict for s in steps] == [Verdict.ERROR, Verdict.PROVED] and steps[-1].arguments["code"] == "x\n  good"
    assert repair_pairs(steps) == [{"broken": "x\n  bad", "diagnostics": steps[0].result.feedback(), "fixed": "x\n  good"}]


def test_repair_falls_back_to_the_model_with_localized_errors():
    lean = Fixed("lean", lambda c: (Verdict.PROVED,) if c == "fixed" else (Verdict.ERROR, "e", _messages(1)))
    client = ScriptedClient([fenced("still bad"), fenced("fixed")])
    steps = repair(lean, "broken", llm=LLM(client, "m"), rounds=3)
    assert [s.arguments["code"] for s in steps] == ["broken", "still bad", "fixed"]
    assert ">>   1 | broken" in client.seen[0]["messages"][-1]["content"]


def _holey_prover(code):
    """'bad' anywhere -> error; open holes -> unknown, each goal being its hole's line; else proved."""
    if "bad" in code:
        return (Verdict.ERROR,)
    goals = [code[code.rfind("\n", 0, at) + 1 : code.find("\n", at) % (len(code) + 1)].strip() for at in holes(code)]
    return (Verdict.UNKNOWN, code, {"goals": goals}) if goals else (Verdict.PROVED,)


def test_decompose_recurses_into_sketches():
    b = Fixed("toyprover", _holey_prover)  # no automation registered: only the model can close holes

    def reply(kwargs):
        prompt = kwargs["messages"][-1]["content"]
        if "too hard" in prompt:  # asked for a sketch of an open hole
            return fenced("have h : X := by sorry\nexact h")
        if "Goal:" in prompt and "X" not in prompt:  # direct proof attempts of the top goal fail
            return fenced("bad")
        return fenced("closed")  # subgoals are easy

    client = ScriptedClient([reply] * 20)
    out = decompose(LLM(client, "m"), b, "theorem t := by\n  sorry", depth=2, width=1)
    assert out.proved and "have h : X := by closed" in out.code


def test_mix_suggest_probe():
    b = Countdown()
    root = b.start("3")
    assert mix(lambda s: ["1", "2"], lambda s: ["2", "3"])(root) == ["1", "2", "3"]
    ranked = suggest(root, lambda s: ["9", "1", "3"])
    assert [c.solved for c in ranked] == [True, False] and all(not c.failed for c in ranked)
    assert probe(root, ["1", "3", "9"]) == {"1": "progress", "3": "solved", "9": "error"}
    assert automation(b)(root) == []  # no automation registered for this toy


def test_step_search_under_budget_and_trace():
    b, trace = Countdown(), Trace()
    with observe(trace):
        step_search(b.start("6"), lambda s: ["3", "4"], budget=10)
    assert {t["outcome"] for t in trace.tactics()} >= {"solved", "error"}


# -- synthesize ------------------------------------------------------------------------------


def test_houdini_prunes_blamed_candidates():
    truth = {"x >= 0", "x <= 10"}

    def check(pairs):
        failing = [label for label, c in pairs if c not in truth]
        if failing:
            return Result(Verdict.REFUTED, "", {"core": failing})
        return Result(Verdict.PROVED)

    out = houdini(["x >= 0", "x < 0", "x <= 10", "x == 3", "x >= 0"], check)
    assert out.proved and out.kept == ["x >= 0", "x <= 10"] and out.rounds == 2


def test_houdini_stops_when_nothing_is_blamed():
    out = houdini(["a"], lambda pairs: Result(Verdict.REFUTED, "property fails", {"core": ["main.assertion.1"]}))
    assert not out.proved and out.kept == ["a"]


def test_assume_and_discharge():
    proposals = iter(["weak", "strong"])
    under = lambda a: Result(Verdict.PROVED if a in ("strong", "false") else Verdict.REFUTED, backend="v")  # noqa: E731
    holds = lambda a: Result(Verdict.PROVED if a == "strong" else Verdict.REFUTED, backend="v")  # noqa: E731
    loop = assume_and_discharge(lambda history: next(proposals), under, holds)
    assert loop.candidate == "strong" and [s.arguments["obligation"] for s in loop.steps] == [
        "goal under assumption", "goal under assumption", "assumption"]  # fmt: skip


def test_assume_and_discharge_never_accepts_an_undischarged_assumption():
    loop = assume_and_discharge(lambda h: "false", lambda a: Result(Verdict.PROVED),
                                lambda a: Result(Verdict.REFUTED), rounds=3)  # fmt: skip
    assert not loop.ok and len(loop.steps) == 6


# -- check ----------------------------------------------------------------------------------------


def test_label_and_best_of():
    def s(v, out="x"):
        return Step("b", {"code": out}, Result(v, out))

    assert label(Result(Verdict.ERROR)) == "malformed" and label(Result(Verdict.UNSAT)) == "unsatisfiable"
    assert label(Result(Verdict.SAT, "a")) == "promising" and label(Result(Verdict.SAT, "a"), lambda r: False) == "wrong"
    steps = [s(Verdict.ERROR), s(Verdict.SAT, "wrong"), s(Verdict.UNKNOWN), s(Verdict.SAT, "right")]
    assert best_of(steps, check=lambda r: r.output == "right").arguments["code"] == "right"
    assert best_of([]) is None


# -- learn --------------------------------------------------------------------------------------


def test_rewards():
    assert binary()(Result(Verdict.PROVED)) == 1.0 and binary()(Result(Verdict.SAT)) == 0.0
    assert binary([Verdict.SAT, Verdict.UNSAT])(Result(Verdict.UNSAT)) == 1.0
    assert [compiles()(Result(v)) for v in (Verdict.PROVED, Verdict.UNKNOWN, Verdict.ERROR)] == [1.0, 0.2, 0.0]


def test_rollouts_are_grouped_and_rewarded_by_the_checker(tmp_path):
    b = Fixed("lean", lambda code: (Verdict.PROVED,) if code == "good" else (Verdict.ERROR,))
    client = ScriptedClient([lambda kw: fenced("good" if "p1" in kw["messages"][-1]["content"] else "bad")] * 4)
    groups = rollouts(LLM(client, "m"), b, ["p1", "p2"], k=2)
    assert [[r.reward for r in g] for g in groups] == [[1.0, 1.0], [0.0, 0.0]]
    assert all(s["temperature"] == 1.0 for s in client.seen)
    rows = to_rl_rows(groups)
    assert write_jsonl(tmp_path / "rl.jsonl", rows) == 4
    assert json.loads((tmp_path / "rl.jsonl").read_text().splitlines()[0])["group"] == 0


def test_prefix_labels():
    code = "a\nb\nc"
    assert [x["label"] for x in prefix_labels(code, Result(Verdict.ERROR, "", _messages(2)))] == ["good", "bad", "bad"]
    assert {x["label"] for x in prefix_labels(code, Result(Verdict.PROVED))} == {"good"}
    assert prefix_labels(code, Result(Verdict.ERROR, "no location")) is None


def test_curriculum_prefers_the_right_difficulty():
    c = Curriculum({"easy": "", "hard": "", "mid": "", "new": ""})
    for _ in range(8):
        c.record("hard", False)
    c.record("mid", True)
    c.record("mid", False)
    for _ in range(3):
        c.record("easy", True)
    assert c.pick(4, include_solved=True)[:2] == ["mid", "new"] and c.pick(4)[0] == "new"
    assert c.pick(4, include_solved=True) == ["mid", "new", "easy", "hard"]  # never solved = hardest, last
    assert c.solved() == ["easy", "mid"] and c.rate("hard") == 0.0 and c.rate("new") is None


def test_expert_iteration_accumulates_verified_solutions_and_trains():
    solvable = {"p1", "p2"}
    trained = []

    def attempt(statement):
        return Step("lean", {"code": statement}, Result(Verdict.PROVED if statement in solvable else Verdict.ERROR))

    run = expert_iteration({"a": "p1", "b": "p2", "c": "p3"}, attempt, train=trained.append, rounds=2, per_round=10)
    assert set(run.dataset) == {"a", "b"} and run.history[0] == {"attempted": 3, "new": 2, "total": 2, "errors": 0}
    assert run.history[1] == {"attempted": 1, "new": 0, "total": 2, "errors": 0}  # only the unsolved one is retried
    assert len(trained) == 1 and len(trained[0]) == 2


def test_evaluate_by_execution():
    b = Fixed("clingo", lambda code: (Verdict.ERROR,) if code == "bad" else (Verdict.SAT, code))
    report = evaluate({"x": "a", "y": "bad", "z": "c"}, lambda p: Step("clingo", {"code": p}, b.run(p)),
                      judge=lambda problem, step: step.result.output == "a")  # fmt: skip
    assert (report.valid, report.decisive, report.correct) == (2, 2, 1)
    assert report.rates()["executable"] == pytest.approx(2 / 3)
