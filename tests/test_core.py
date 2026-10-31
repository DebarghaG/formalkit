"""Core tests: no Docker needed. A toy adapter is served in-process."""

from __future__ import annotations

import json
import threading
from pathlib import Path

import pytest

from formalkit import Agent, Remote, Result, Spec, Verdict
from formalkit.adapters._smtlib import classify
from formalkit.agent import parse_tool_calls
from formalkit.server import Adapter, execute, make_server, sh, workdir
from conftest import ScriptedClient, call


class Toy(Adapter):
    """'proved' iff the code is 'true'; errors on anything but true/false."""

    spec = Spec(
        name="toy", family="Test", language="booleans", emits="true or false",
        authority="truth", feedback="nothing", use="tests",
        inputs={"note": "free text", "hint": "optional text"}, optional=["hint"],
    )  # fmt: skip

    def run(self, code, timeout, **inputs):
        if code == "boom":
            raise RuntimeError("kaboom")
        if code not in ("true", "false"):
            return Result(Verdict.ERROR, f"parse error: {code!r}")
        return Result(Verdict.PROVED if code == "true" else Verdict.REFUTED, code, {"inputs": inputs})


@pytest.fixture(scope="module")
def toy() -> Remote:
    server = make_server(Toy(), "127.0.0.1", 0)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    yield Remote("toy", f"http://127.0.0.1:{server.server_address[1]}")
    server.shutdown()


def test_verdict_decisive():
    assert {v for v in Verdict if v.decisive} == {"proved", "refuted", "sat", "unsat", "optimal"}


def test_result_roundtrip_and_feedback():
    r = Result(Verdict.SAT, "x" * 10_000, {"model": {"x": 1}}, "z3", 0.1)
    assert Result.from_dict(json.loads(json.dumps(r.to_dict()))) == r
    fb = r.feedback(limit=100)
    assert fb.startswith("verdict: sat") and "truncated" in fb and len(fb) < 200


def test_execute_never_raises():
    r = execute(Toy(), "boom")
    assert r.verdict is Verdict.ERROR and "kaboom" in r.output and r.backend == "toy"


def test_sh_timeout_kills_process_group():
    proc = sh("sleep 30 & sleep 30", timeout=0.5)
    assert proc.timed_out


def test_workdir_writes_files():
    with workdir({"a/b.txt": "hi"}) as d:
        assert (d / "a/b.txt").read_text() == "hi"


@pytest.mark.parametrize(
    "out,verdict",
    [
        ("sat", Verdict.SAT),
        ("unsat\n(error \"model is not available\")", Verdict.UNSAT),  # post-verdict error is harmless
        ("(error \"unknown constant y\")\nsat", Verdict.ERROR),  # pre-verdict error poisons it
        ("sat\nunsat", Verdict.UNSAT),  # last verdict wins
        ("unknown", Verdict.UNKNOWN),
        ("", Verdict.ERROR),
    ],
)
def test_smtlib_classify(out, verdict):
    assert classify(out).verdict is verdict


def test_smtlib_drops_no_model_noise_after_unsat():
    assert classify('unsat\n(error "line 3 column 10: model is not available")').output == "unsat"


def test_backend_protocol(toy):
    assert toy.spec.name == "toy"
    r = toy.run("true", note="hello")
    assert r.verdict is Verdict.PROVED and r.details["inputs"] == {"note": "hello"} and r.backend == "toy"
    assert toy.call('{"code": "false", "note": "x"}').verdict is Verdict.REFUTED


def test_tool_styles(toy):
    oa, an, mcp = toy.tool("openai"), toy.tool("anthropic"), toy.tool("mcp")
    assert oa["function"]["parameters"]["required"] == ["code", "note"]
    assert an["input_schema"] == mcp["inputSchema"] == oa["function"]["parameters"]


def test_malformed_tool_calls_are_explained(toy):
    assert "missing the required argument 'code'" in toy.call({}).output
    assert "'code' must be a string" in toy.call({"code": 3, "note": "n"}).output
    assert "unknown argument(s) ['extra']" in toy.call({"code": "true", "note": "n", "extra": 1}).output
    assert "missing required argument(s) ['note']" in toy.call({"code": "true"}).output
    assert "not a JSON object" in toy.call("{oops").output and "must be a JSON object" in toy.call("[1]").output
    assert toy.call({"code": "true", "note": "n", "hint": None}).verdict is Verdict.PROVED  # optional, omitted


def test_unreachable_backend_is_an_error_result():
    assert Remote("nope", "http://127.0.0.1:9").run("x").verdict is Verdict.ERROR


def test_parse_tool_calls():
    hermes = '<tool_call>{"name": "z3", "arguments": {"code": "(check-sat)"}}</tool_call>'
    qwen = "<tool_call><function=finish><parameter=answer>Yes</parameter></function></tool_call>"
    calls = parse_tool_calls(hermes + qwen)
    assert [c["function"]["name"] for c in calls] == ["z3", "finish"]
    assert json.loads(calls[1]["function"]["arguments"]) == {"answer": "Yes"}


# -- agent loop with a scripted LLM ------------------------------------------------


def test_agent_verified_answer(toy):
    llm = ScriptedClient([("", [call("toy", note="n", code="nonsense")]), ("", [call("toy", note="n", code="true"), call("finish", answer="Yes")])])
    ans = Agent(llm, "m", [toy]).solve("q?")
    assert ans.answer == "Yes" and ans.verified and ans.verdict is Verdict.PROVED
    assert [s.result.verdict for s in ans.steps] == [Verdict.ERROR, Verdict.PROVED]
    assert ans.usage["total_tokens"] == 20
    assert {t["function"]["name"] for t in llm.seen[0]["tools"]} == {"toy", "finish"}


def test_agent_rejects_unverified_finish_then_accepts(toy):
    llm = ScriptedClient([("", [call("finish", answer="No")])] * 3)
    ans = Agent(llm, "m", [toy], max_finish_rejections=2).solve("q?")
    assert ans.answer == "No" and not ans.verified and ans.evidence == [] and ans.iterations == 3
    assert sum("REJECTED" in str(m.get("content")) for m in ans.messages) == 2


def test_agent_nudges_and_recovers_textual_calls(toy):
    text = '<tool_call>{"name": "toy", "arguments": {"code": "true", "note": "n"}}</tool_call>'
    llm = ScriptedClient([("thinking...", []), (text, []), ("", [call("finish", answer="Yes")])])
    ans = Agent(llm, "m", [toy]).solve("q?")
    assert ans.verified and ans.answer == "Yes" and ans.iterations == 3


def test_agent_grace_turn_after_final_proof(toy):
    llm = ScriptedClient([("", [call("toy", note="n", code="true")]), ("", [call("finish", answer="Yes")])])
    ans = Agent(llm, "m", [toy], max_iterations=1).solve("q?")
    assert ans.verified and ans.iterations == 2


def test_answer_evidence_is_rerunnable(toy):
    llm = ScriptedClient([("", [call("toy", note="n", code="true"), call("finish", answer="Yes")])])
    ans = Agent(llm, "m", [toy]).solve("q?")
    assert [(s.backend, s.arguments) for s in ans.evidence] == [("toy", {"note": "n", "code": "true"})]
    assert ans.recheck()
    assert json.loads(json.dumps(ans.to_dict()))["evidence"][0]["result"]["verdict"] == "proved"


@pytest.mark.parametrize("name", sorted(__import__("formalkit").BACKENDS))
def test_every_registered_backend_has_a_consistent_adapter(name):
    from formalkit import docker
    from formalkit.server import load

    spec = load(name).spec
    assert spec.name == name
    assert all([spec.language, spec.emits, spec.authority, spec.feedback, spec.use, spec.guidance])
    assert set(spec.optional) <= set(spec.inputs)
    assert docker.dockerfile(name).exists()
    assert (Path(__file__).parent.parent / "examples" / name).is_dir(), "add examples/<name>/<verdict>-*.ext"
