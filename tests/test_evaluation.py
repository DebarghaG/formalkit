"""Per-stage evaluation, consensus with abstention, and the runtime policy guard."""

from __future__ import annotations

import pytest
from conftest import Fixed, ScriptedClient, call

from formalkit import LLM, Agent, Guard, Result, Verdict, backend, docker
from formalkit.agent import Answer, Step
from formalkit.learn import evaluate
from formalkit.patterns import consensus

# -- per-stage evaluation ------------------------------------------------------------------


def _step(verdict, code="x"):
    return Step("b", {"code": code}, Result(verdict))


def test_each_stage_is_measured_separately():
    outcomes = {
        "runs_wrong": _step(Verdict.SAT, "wrong"),  # executable, decisive, verified, but wrong: a false accept
        "runs_right": _step(Verdict.UNSAT, "right"),
        "broken": _step(Verdict.ERROR),
        "undecided": _step(Verdict.UNKNOWN, "right"),
    }
    report = evaluate(outcomes, lambda step: step, judge=lambda problem, step: step.arguments["code"] == "right",
                      fidelity=lambda problem, step: step.result.verdict is not Verdict.ERROR)  # fmt: skip
    r = report.rates()
    assert (r["executable"], r["decisive"], r["verified"]) == (0.75, 0.5, 0.5)
    assert r["correct"] == 0.5 and r["false_accept"] == 0.25 and r["faithful"] == 0.75
    assert [a.false_accept for a in report.attempts] == [True, False, False, False]


def test_pass_at_k_and_pass_hat_k_measure_reliability():
    flips = {"steady": iter([True, True, True]), "flaky": iter([True, False, True]), "never": iter([False] * 3)}

    def solve(problem):
        return _step(Verdict.SAT, "right" if next(flips[problem]) else "wrong")

    report = evaluate({p: p for p in flips}, solve, judge=lambda p, s: s.arguments["code"] == "right", k=3, workers=1)
    r = report.rates()
    assert r["pass@k"] == pytest.approx(2 / 3) and r["pass^k"] == pytest.approx(1 / 3)
    assert "pass^k" in report.summary("demo") and report.total == 9


def test_evaluate_scores_agent_answers_and_repairs():
    ans = Answer("q", answer="42", verified=True, evidence=[_step(Verdict.UNSAT)],
                 steps=[_step(Verdict.ERROR), _step(Verdict.ERROR), _step(Verdict.UNSAT)], usage={"total_tokens": 99})  # fmt: skip
    a = evaluate({"q": "q"}, lambda p: ans, judge=lambda p, x: x.answer == "42").attempts[0]
    assert (a.verified, a.correct, a.repairs, a.tokens) == (True, True, 2, 99)


def test_a_crashing_attempt_fails_every_stage():
    def solve(problem):
        raise RuntimeError("api down")

    a = evaluate({"p": 1}, solve, judge=lambda p, s: True).attempts[0]
    assert not (a.executable or a.decisive or a.verified) and a.correct is False and "api down" in a.error


# -- consensus with abstention ------------------------------------------------------------------


def _answer(text, verified=True):
    return Answer("q", answer=text, verified=verified)


def test_consensus_answers_when_verified_attempts_agree():
    outs = iter([_answer("Bob"), _answer("bob "), _answer("Carol"), _answer("Bob"), _answer("Bob", verified=False)])
    c = consensus(lambda: next(outs), n=5, threshold=0.6, workers=1)
    assert c.answer == "bob" and c.confidence == 0.6 and not c.abstained and c.counts == {"bob": 3, "carol": 1}


def test_consensus_abstains_on_disagreement_ties_and_unverified_answers():
    outs = iter([_answer("A"), _answer("B"), _answer("A"), _answer("B")])
    assert consensus(lambda: next(outs), n=4, threshold=0.5, workers=1).abstained  # tie
    outs = iter([_answer("A", verified=False)] * 5)
    c = consensus(lambda: next(outs), n=5, workers=1)
    assert c.abstained and c.answer is None and c.confidence == 0.0
    outs = iter([_answer("A"), None, None, None, None])
    assert consensus(lambda: next(outs), n=5, threshold=0.6, workers=1).abstained  # 1 of 5 is not enough


# -- the runtime guard ----------------------------------------------------------------------------

POLICY = """(set-option :produce-unsat-cores true)
(declare-const amount Int)
(declare-const balance Int)
(declare-const verified Bool)
(declare-const sanctioned Bool)
(assert (! (<= amount balance) :named within_balance))
(assert (! (=> (> amount 1000) verified) :named large_needs_verification))
(assert (! (not sanctioned) :named no_sanctioned_payee))
(assert (! (> amount 0) :named positive_amount))"""


def _encode(name, args):
    if name != "transfer":
        return None
    return (f"(assert (= amount {int(args['amount'])}))\n(assert (= balance {int(args['balance'])}))\n"
            f"(assert (= verified {str(bool(args.get('verified'))).lower()}))\n"
            f"(assert (= sanctioned {str(args['to'] in {'acct-666'}).lower()}))")  # fmt: skip


def _smt_policy_backend():
    """A toy stand-in for z3 that evaluates this policy in Python (the Docker test uses real z3)."""

    def run(code):
        import re

        vals = dict(re.findall(r"\(= (\w+) (\w+)\)", code))
        amount, balance = int(vals["amount"]), int(vals["balance"])
        broken = [n for n, ok in [("within_balance", amount <= balance),
                                  ("large_needs_verification", amount <= 1000 or vals["verified"] == "true"),
                                  ("no_sanctioned_payee", vals["sanctioned"] == "false"),
                                  ("positive_amount", amount > 0)] if not ok]  # fmt: skip
        return (Verdict.UNSAT, "unsat", {"core": broken}) if broken else (Verdict.SAT, "sat")

    return Fixed("z3", run, language="SMT-LIB 2.6")


def test_guard_allows_compliant_actions_and_names_violated_rules():
    guard = Guard(_smt_policy_backend(), POLICY, _encode)
    assert guard.check("transfer", {"to": "acct-1", "amount": 50, "balance": 100}).allowed
    d = guard.check("transfer", {"to": "acct-666", "amount": 5000, "balance": 100})
    assert not d.allowed and "within_balance" in d.reason and "no_sanctioned_payee" in d.reason
    assert guard.check("get_balance", {}).allowed  # not governed by the policy
    assert (guard.checked, guard.blocked) == (3, 1)


def test_guard_fails_closed():
    inconclusive = Guard(Fixed("z3", lambda c: (Verdict.UNKNOWN,), language="SMT-LIB 2.6"), POLICY, _encode)
    assert not inconclusive.check("transfer", {"to": "a", "amount": 1, "balance": 9}).allowed
    broken_encoder = Guard(_smt_policy_backend(), POLICY, lambda n, a: 1 / 0)
    d = broken_encoder.check("transfer", {})
    assert not d.allowed and "ZeroDivisionError" in d.reason


def test_agent_guard_blocks_before_execution():
    ran = []
    tool = Fixed("transfer", lambda code: (ran.append(code) or Verdict.SAT,))
    guard = Guard(_smt_policy_backend(), POLICY,
                  lambda name, args: _encode("transfer", {"to": "acct-1", "balance": 100, "amount": args["code"]}))  # fmt: skip
    client = ScriptedClient([("", [call("transfer", code="5000")]), ("", [call("transfer", code="50")]),
                             ("", [call("finish", answer="done", evidence=[1])])])  # fmt: skip
    ans = Agent(LLM(client, "m"), backends=[tool], guard=guard).solve("pay")
    assert ran == ["50"] and len(ans.blocked) == 1 and "within_balance" in ans.blocked[0]["reason"]
    assert any("BLOCKED by policy" in str(m.get("content")) for m in ans.messages)


def test_a_broken_guard_blocks_rather_than_allows():
    ran = []
    tool = Fixed("t", lambda code: (ran.append(code) or Verdict.SAT,))

    def guard(name, args):
        raise RuntimeError("policy server down")

    client = ScriptedClient([("", [call("t", code="x")]), ("", [call("finish", answer="?")])] * 2)
    ans = Agent(LLM(client, "m"), backends=[tool], guard=guard, max_finish_rejections=0).solve("q")
    assert ran == [] and "guard failed" in ans.blocked[0]["reason"]


@pytest.mark.docker
def test_guard_with_real_z3():
    if not docker.has_image("z3"):
        pytest.skip("z3 image not built")
    guard = Guard(backend("z3"), POLICY, _encode)
    assert guard.check("transfer", {"to": "acct-1", "amount": 900, "balance": 1000}).allowed
    d = guard.check("transfer", {"to": "acct-1", "amount": 1500, "balance": 9000})
    assert not d.allowed and d.reason == "violates: large_needs_verification"
    assert guard.check("transfer", {"to": "acct-1", "amount": 1500, "balance": 9000, "verified": True}).allowed
