"""Backend composition, evidence policies, the LLM wrapper and agent hooks (no Docker)."""

from __future__ import annotations

import time

import pytest
from conftest import Fixed, ScriptedClient, call

from formalkit import LLM, Agent, Rejected, Verdict, cited_or_last, compiled, extract_code, nonvacuous, portfolio
from formalkit.agent import Step
from formalkit.core import Result
from formalkit.evidence import drop_last_assert

# -- compiled ----------------------------------------------------------------------


def _upper(text):
    if "!" in text:
        raise ValueError("no shouting")
    return text.upper()


def test_compiled_runs_the_compiled_program():
    inner = Fixed("inner", lambda code: (Verdict.SAT,) if code == "HELLO" else (Verdict.ERROR, "bad"))
    b = compiled(inner, _upper, name="lower", language="lowercase", emits="lowercase text")
    r = b.run("hello")
    assert r.verdict is Verdict.SAT and r.backend == "lower"
    assert r.details["compiled"] == "HELLO" and r.details["via"] == "inner"
    assert b.spec.name == "lower" and b.spec.language == "lowercase" and b.spec.authority == inner.spec.authority


def test_compiled_errors_are_feedback():
    inner = Fixed("inner", lambda code: (Verdict.ERROR, "inner says no"))
    b = compiled(inner, _upper, name="lower", language="lowercase", emits="x")
    assert b.run("hi!").output == "lowercase error: no shouting" and inner.runs == []
    r = b.run("hi")
    assert r.verdict is Verdict.ERROR and "inner says no" in r.output and "1 | HI" in r.output


# -- portfolio ---------------------------------------------------------------------


def _slow(verdict, delay):
    def fn(code):
        time.sleep(delay)
        return (verdict,)

    return fn


def test_portfolio_first_decisive_wins():
    p = portfolio(Fixed("slow", _slow(Verdict.PROVED, 2.0)), Fixed("fast", _slow(Verdict.REFUTED, 0.0)))
    start = time.monotonic()
    r = p.run("x")
    assert r.verdict is Verdict.REFUTED and r.backend == "fast" and time.monotonic() - start < 1.5
    assert r.details["portfolio"] == {"fast": "refuted"}


def test_portfolio_skips_undecided_members():
    p = portfolio(Fixed("a", _slow(Verdict.UNKNOWN, 0)), Fixed("b", _slow(Verdict.UNSAT, 0.2)))
    r = p.run("x")
    assert r.verdict is Verdict.UNSAT and r.details["portfolio"] == {"a": "unknown", "b": "unsat"}


def test_portfolio_without_decision_reports_all():
    p = portfolio(Fixed("a", _slow(Verdict.ERROR, 0)), Fixed("b", _slow(Verdict.UNKNOWN, 0.1)), name="ab")
    r = p.run("x")
    assert r.verdict is Verdict.UNKNOWN and r.backend == "ab" and "[a]" in r.output and "[b]" in r.output


def test_portfolio_requires_one_language():
    with pytest.raises(ValueError, match="language"):
        portfolio(Fixed("a", _slow(Verdict.SAT, 0)), Fixed("b", _slow(Verdict.SAT, 0), language="other"))


# -- evidence ----------------------------------------------------------------------


def _step(verdict, code="c", ref=None):
    return Step("b", {"code": code}, Result(verdict, backend="b"), ref)


def test_cited_or_last():
    steps = [_step(Verdict.UNSAT), _step(Verdict.ERROR), _step(Verdict.SAT)]
    assert cited_or_last(steps, None) == [steps[2]]
    assert cited_or_last(steps, [3, 1]) == [steps[2], steps[0]]
    with pytest.raises(Rejected, match="not decisive"):
        cited_or_last(steps, [2])
    with pytest.raises(Rejected, match="do not exist"):
        cited_or_last(steps, [7])
    with pytest.raises(Rejected, match="no tool run"):
        cited_or_last([], None)


def test_drop_last_assert_respects_comments_strings_and_quoted_symbols():
    script = '(declare-const |a)b| Int)\n(assert (> |a)b| 0)) ; (assert fake)\n(assert (= "x)""y" "z"))\n(check-sat)\n'
    assert drop_last_assert(script) == '(declare-const |a)b| Int)\n(assert (> |a)b| 0)) ; (assert fake)\n\n(check-sat)\n'
    assert drop_last_assert("(check-sat)") is None


def _smt(fn):
    return Fixed("smt", fn, language="SMT-LIB 2.6")


def test_nonvacuous_rejects_contradictory_premises():
    # premises "p" and "(not p)" contradict each other: everything is unsat
    smt = _smt(lambda code: (Verdict.UNSAT,))
    script = "(assert p)\n(assert (not p))\n(assert (not claim))\n(check-sat)"
    with pytest.raises(Rejected, match="vacuous"):
        nonvacuous()([_step(Verdict.UNSAT, script, smt)], None)


def test_nonvacuous_accepts_and_records_the_premise_check():
    smt = _smt(lambda code: (Verdict.UNSAT,) if "claim" in code else (Verdict.SAT,))
    script = "(assert p)\n(assert (not claim))\n(check-sat)"
    evidence = nonvacuous()([_step(Verdict.UNSAT, script, smt)], None)
    assert [s.result.verdict for s in evidence] == [Verdict.SAT, Verdict.UNSAT]
    assert "claim" not in evidence[0].arguments["code"]


# -- LLM ---------------------------------------------------------------------------


class NewOpenAIModel(ScriptedClient):
    def create(self, **kwargs):
        if "max_tokens" in kwargs:
            raise RuntimeError("Error code: 400 - Unsupported parameter: 'max_tokens' is not supported with this "
                               "model. Use 'max_completion_tokens' instead.")  # fmt: skip
        return super().create(**kwargs)


def test_llm_sends_max_tokens_and_a_timeout_by_default():
    client = ScriptedClient([("a", None)])
    LLM(client, "m", max_tokens=99).ask("q")
    assert client.seen[-1]["max_tokens"] == 99 and client.seen[-1]["timeout"] == 600
    assert "max_completion_tokens" not in client.seen[-1]


def test_llm_switches_to_max_completion_tokens_once_when_rejected():
    client = NewOpenAIModel([("a", None), ("b", None)])
    llm = LLM(client, "m", max_tokens=99)
    assert llm.ask("q") == ["a"] and llm.ask("q") == ["b"]
    assert client.seen[-1]["max_completion_tokens"] == 99 and "max_tokens" not in client.seen[-1]
    assert llm.usage["total_tokens"] == 20


def test_llm_samples_and_passes_options():
    client = ScriptedClient([("x", None)] * 3)
    llm = LLM(client, "m", temperature=0.2, reasoning_effort="low")
    assert llm.ask("q", n=3, temperature=0.9) == ["x"] * 3
    assert all(s["temperature"] == 0.9 and s["reasoning_effort"] == "low" for s in client.seen)


def test_extract_code():
    assert extract_code("text\n```smt2\n(a)\n```\nmore\n```\n(b)\n```") == "(b)"
    assert extract_code("  (plain)  ") == "(plain)"


# -- agent hooks ---------------------------------------------------------------------


def test_agent_answer_backed_by_several_cited_runs():
    smt = _smt(lambda code: (Verdict.SAT,) if "3" in code else (Verdict.UNSAT,))
    client = ScriptedClient([
        ("", [call("smt", code="colors 2")]),
        ("", [call("smt", code="colors 3")]),
        ("", [call("finish", answer="3", evidence=[1, 2])]),
    ])  # fmt: skip
    ans = Agent(LLM(client, "m"), backends=[smt]).solve("min colors?")
    assert ans.verified and [s.result.verdict for s in ans.evidence] == [Verdict.UNSAT, Verdict.SAT]
    assert "smt: unsat, smt: sat" in str(ans)
    assert ans.recheck()


def test_agent_hooks_render_nudge_on_step_and_policy():
    smt = _smt(lambda code: (Verdict.UNSAT,))
    seen = []
    client = ScriptedClient([
        ("thinking", []),
        ("", [call("smt", code="(assert p)\n(assert (not p))")]),
        ("", [call("finish", answer="Yes")]),
        ("", [call("finish", answer="Yes")]),
    ])  # fmt: skip
    agent = Agent(
        LLM(client, "m"), backends=[smt], evidence=nonvacuous(), max_finish_rejections=1,
        render=lambda r: f"VERDICT={r.verdict}", nudge=lambda steps: "CUSTOM NUDGE", on_step=seen.append,
    )  # fmt: skip
    ans = agent.solve("q")
    contents = [m.get("content") for m in ans.messages]
    assert "CUSTOM NUDGE" in contents and "run #1\nVERDICT=unsat" in contents
    assert any("vacuous" in str(c) for c in contents)
    assert [s.backend for s in seen] == ["smt"]
    assert ans.answer == "Yes" and not ans.verified  # rejection budget spent: accepted, unverified


def test_agent_tolerates_sloppy_evidence_citations():
    smt = _smt(lambda code: (Verdict.UNSAT,))
    client = ScriptedClient([("", [call("smt", code="x"), call("finish", answer="ok", evidence="#1")])])
    assert Agent(LLM(client, "m"), backends=[smt]).solve("q").verified
