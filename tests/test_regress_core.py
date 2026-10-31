"""Regressions found by live testing of the core (agent, client, docker lifecycle, observers)."""

from __future__ import annotations

import subprocess
import sys

import pytest
from conftest import Fixed, ScriptedClient, call

from formalkit import LLM, Agent, Budget, Remote, Verdict, backend, docker, observe

# -- budget inside the agent ---------------------------------------------------------------


def test_agent_returns_partial_answer_when_budget_runs_out_in_a_tool_call():
    b = Fixed("b", lambda code: (Verdict.UNKNOWN,))
    client = ScriptedClient([("", [call("b", code="x")])] * 5)
    with observe(Budget(calls=2)):
        ans = Agent(LLM(client, "m"), backends=[b], max_iterations=5).solve("q")
    assert ans.answer is None and "budget exceeded: calls" in ans.error and len(ans.steps) == 2


def test_agent_reports_budget_not_llm_failure_when_tokens_run_out():
    b = Fixed("b", lambda code: (Verdict.UNKNOWN,))
    client = ScriptedClient([("", [call("b", code="x")])] * 5)
    with observe(Budget(tokens=15)):
        ans = Agent(LLM(client, "m"), backends=[b], max_iterations=5).solve("q")
    assert ans.error.startswith("budget exceeded: tokens") and "LLM call failed" not in ans.error


# -- lifecycle ------------------------------------------------------------------------------


def test_unmanaged_remote_never_restarts_anything():
    r = Remote("nothing-here", "http://127.0.0.1:9").run("x")
    assert r.verdict is Verdict.ERROR and "could not reach" in r.output


@pytest.mark.docker
def test_managed_backend_restarts_after_its_container_dies():
    if not docker.has_image("z3"):
        pytest.skip("z3 image not built")
    z3 = backend("z3")
    assert z3.managed and z3.run("(check-sat)").verdict is Verdict.SAT
    subprocess.run(["docker", "kill", docker.container("z3")], capture_output=True)
    assert z3.run("(check-sat)").verdict is Verdict.SAT  # restarted transparently


@pytest.mark.docker
def test_concurrent_first_use_shares_one_container():
    if not docker.has_image("cvc5"):
        pytest.skip("cvc5 image not built")
    docker.down("cvc5")
    code = "import formalkit; print(formalkit.backend('cvc5').run('(check-sat)').verdict)"
    procs = [subprocess.Popen([sys.executable, "-c", code], stdout=subprocess.PIPE, text=True) for _ in range(6)]
    outputs = [p.communicate(timeout=120)[0].strip() for p in procs]
    assert outputs == ["sat"] * 6
    names = subprocess.run(["docker", "ps", "--filter", f"name={docker.container('cvc5')}", "--format", "{{.Names}}"],
                           capture_output=True, text=True).stdout.split()  # fmt: skip
    assert names == [docker.container("cvc5")]


# -- MCP protocol ---------------------------------------------------------------------------


def test_mcp_answers_every_request_and_explains_bad_calls(monkeypatch, capsys):
    import io
    import json

    from formalkit import mcp

    lines = [
        {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-06-18"}},
        "not json",
        [{"jsonrpc": "2.0", "id": 2, "method": "ping"}],
        {"jsonrpc": "2.0", "method": "notifications/initialized"},
        {"jsonrpc": "2.0", "id": 3, "method": "tools/list"},
        {"jsonrpc": "2.0", "id": 4, "method": "tools/call", "params": {"name": "b", "arguments": {}}},
        {"jsonrpc": "2.0", "id": 5, "method": "tools/call", "params": {"name": "b", "arguments": {"code": "x"}}},
        {"jsonrpc": "2.0", "id": 6, "method": "tools/call", "params": {"name": "zz", "arguments": {"code": "x"}}},
        {"jsonrpc": "2.0", "id": 7, "method": "resources/list"},
    ]
    text = "\n".join(line if isinstance(line, str) else json.dumps(line) for line in lines) + "\n"
    monkeypatch.setattr("sys.stdin", io.StringIO(text))
    mcp.serve([Fixed("b", lambda code: (Verdict.SAT,))])
    replies = [json.loads(line) for line in capsys.readouterr().out.splitlines()]
    by_id = {r["id"]: r for r in replies if r["id"] is not None}
    errors = [r["error"]["code"] for r in replies if r["id"] is None]
    assert errors == [-32700, -32600]  # parse error, then batch rejected
    assert by_id[1]["result"]["serverInfo"]["name"] == "formalkit"
    assert [t["name"] for t in by_id[3]["result"]["tools"]] == ["b"]
    assert "missing the required argument 'code'" in by_id[4]["result"]["content"][0]["text"]
    assert by_id[5]["result"]["structuredContent"]["verdict"] == "sat"
    assert by_id[6]["result"]["isError"] and by_id[7]["error"]["code"] == -32601


# -- pinned statements: the model may only fill the hole ------------------------------------


def test_pin_fills_only_the_hole():
    from formalkit.patterns import pin

    fill = pin("theorem t (a : Nat) : a = a := by\n  sorry -- the proof\n")
    assert fill("by\n  rfl") == "theorem t (a : Nat) : a = a := by\n  rfl -- the proof\n"
    assert fill("cases a\n· rfl\n· rfl") == "theorem t (a : Nat) : a = a := by\n  cases a\n  · rfl\n  · rfl -- the proof\n"
    # Text that tries to restate or add a theorem stays inside the proof block (and fails to check there).
    sneaky = fill("rfl\ntheorem other : True := trivial")
    assert sneaky.startswith("theorem t (a : Nat) : a = a := by\n  rfl\n  theorem other")
    with pytest.raises(ValueError, match="exactly one"):
        pin("theorem a : P := sorry\ntheorem b : Q := sorry")


def test_refine_with_template_cannot_change_the_statement():
    from formalkit.patterns import refine

    seen = []
    lean = Fixed("lean", lambda code: (seen.append(code) or Verdict.PROVED if "2 + 2 = 5 := by\n  decide" not in code
                                       else Verdict.ERROR,))  # fmt: skip
    # The model "proves" the negation instead: with a template that text can only land in the hole.
    client = ScriptedClient([("```lean\ntheorem t_not : ¬ (2 + 2 = 5) := by decide\n```", None)])
    steps = refine(LLM(client, "m"), lean, "Prove it.", template="theorem t : 2 + 2 = 5 := by\n  sorry", rounds=1)
    assert steps[0].arguments["code"].startswith("theorem t : 2 + 2 = 5 := by\n  theorem t_not")
    assert "ONLY the text that replaces `sorry`" in client.seen[0]["messages"][1]["content"]


def test_pinned_rollouts_reward_only_the_asked_statement():
    from formalkit.learn import rollouts

    lean = Fixed("lean", lambda code: (Verdict.PROVED,) if code.startswith("theorem t : True := by\n  trivial") else (Verdict.ERROR,))
    client = ScriptedClient([("```\ntrivial\n```", None)] * 2)
    groups = rollouts(LLM(client, "m"), lean, ["theorem t : True := by\n  sorry"], k=2, pinned=True)
    assert [r.reward for r in groups[0]] == [1.0, 1.0]


# -- CLI errors are messages, not tracebacks -------------------------------------------------


@pytest.mark.parametrize(
    "argv,message",
    [
        (["run", "nosuch", "-"], "unknown backend 'nosuch'"),
        (["spec", "nosuch"], "known: z3"),
        (["build", "pot"], "'pot' is a virtual backend"),
        (["run", "z3", "/no/such/file", "--url", "http://127.0.0.1:9"], "No such file or directory: /no/such/file"),
    ],
)
def test_cli_errors(argv, message, capsys):
    from formalkit.cli import main

    with pytest.raises(SystemExit) as exit_info:
        main(argv)
    assert message in str(exit_info.value.code)


def test_answer_usage_is_per_answer_even_with_a_shared_llm():
    from concurrent.futures import ThreadPoolExecutor

    b = Fixed("b", lambda code: (Verdict.UNSAT,))
    llm = LLM(ScriptedClient([("", [call("b", code="x"), call("finish", answer="ok")])] * 8), "m")
    agent = Agent(llm, backends=[b])
    with ThreadPoolExecutor(8) as pool:
        answers = list(pool.map(lambda _: agent.solve("q"), range(8)))
    assert [a.usage["total_tokens"] for a in answers] == [10] * 8 and llm.usage["total_tokens"] == 80


def test_vacuity_check_drops_the_named_goal_not_a_later_premise():
    from formalkit.evidence import drop_last_assert

    script = "(assert p)\n(assert (! (not claim) :named goal))\n(assert q)\n(check-sat)"
    assert drop_last_assert(script) == "(assert p)\n\n(assert q)\n(check-sat)"
    assert drop_last_assert("(assert p)\n(assert (! r :named goals))") == "(assert p)\n"  # not 'goal': last
    assert drop_last_assert("(assert p)\n(assert (! (not c) :named |goal|))") == "(assert p)\n"


def test_layouts_cover_hole_relative_and_file_level_indentation():
    from formalkit.patterns.generate import layouts

    file_level = "rw [foo]\n  have h : P := by\n    omega\n  exact h"
    assert layouts(file_level, 2) == ["rw [foo]\nhave h : P := by\n  omega\nexact h", file_level]
    relative = "have h : P := by\n  omega\nexact h"
    assert layouts(relative, 2) == [relative]  # a line at column 0: already relative
    assert layouts("simp", 2) == ["simp"] and layouts("a\n  b", 0) == ["a\n  b"]


@pytest.mark.docker
def test_pinned_fill_with_file_level_indentation_checks_in_lean():
    if not docker.has_image("lean"):
        pytest.skip("lean image not built")
    from formalkit.patterns import pin

    fill = pin("theorem t (n : Nat) : n + 0 = n ∧ 0 + n = n := by\n  sorry")
    text = "constructor\n  · simp\n  · simp"  # as models write it: continuation lines at file indentation
    verdicts = [backend("lean").run(code).verdict for code in fill.variants(text)]
    assert verdicts[0] is Verdict.PROVED


def test_tool_names_are_valid_for_every_tool_api():
    import re

    weird = Fixed("my backend+v2/ü", lambda code: (Verdict.SAT,))
    assert weird.tool_name == "my_backend_v2__"
    for style, key in (("openai", lambda t: t["function"]["name"]), ("anthropic", lambda t: t["name"]),
                       ("mcp", lambda t: t["name"])):  # fmt: skip
        assert re.fullmatch(r"[A-Za-z0-9_-]{1,64}", key(weird.tool(style)))
    # The agent routes the sanitized name back to the backend and records the real name.
    client = ScriptedClient([("", [call("my_backend_v2__", code="x"), call("finish", answer="ok")])])
    ans = Agent(LLM(client, "m"), backends=[weird]).solve("q")
    assert ans.verified and ans.steps[0].backend == "my backend+v2/ü"


# -- the server never drops a connection --------------------------------------------------------


@pytest.mark.parametrize(
    "body,status,message",
    [
        (b'{"code": "x", "timeout": "abc"}', 400, "'timeout' must be a number"),
        (b'{"code": "x", "timeout": NaN}', 400, "'timeout' must be a number"),
        (b"[1, 2]", 400, "must be a JSON object"),
        (b'{"code": "x", "inputs": [1]}', 400, "'inputs' must be an object"),
        (b'{"code": "x", "inputs": {"a": 1}}', 400, "'inputs' must be an object"),
        (b'{"code": 5}', 400, "'code' must be a string"),
        (b"{nope", 400, "bad request"),
    ],
)
def test_server_rejects_malformed_requests_cleanly(body, status, message):
    import threading
    import urllib.request

    from formalkit.server import Adapter, make_server
    from formalkit.core import Result, Spec

    class Echo(Adapter):
        spec = Spec(name="echo", family="t", language="t", emits="", authority="", feedback="", use="")

        def run(self, code, timeout, **inputs):
            return Result(Verdict.SAT, code)

    server = make_server(Echo(), "127.0.0.1", 0)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    try:
        req = urllib.request.Request(f"http://127.0.0.1:{server.server_address[1]}/run", data=body)
        with pytest.raises(urllib.error.HTTPError) as err:
            urllib.request.urlopen(req, timeout=10)
        assert err.value.code == status and message in err.value.read().decode()
    finally:
        server.shutdown()


def test_rerun_ignores_bookkeeping_arguments():
    from formalkit.agent import Step

    b = Fixed("b", lambda code: (Verdict.PROVED,))
    step = Step("b", {"code": "x", "fill": "y", "obligation": "goal"}, b.run("x"), b)
    assert step.rerun().verdict is Verdict.PROVED and b.runs[-1] == "x"


def test_llm_drops_temperature_for_models_that_reject_it():
    class Strict(ScriptedClient):
        def create(self, **kwargs):
            if "temperature" in kwargs:
                raise RuntimeError("Error code: 400 - Unsupported value: 'temperature' does not support 0.8 "
                                   "with this model. Only the default (1) value is supported.")  # fmt: skip
            return super().create(**kwargs)

    client = Strict([("a", None), ("b", None)])
    llm = LLM(client, "m", temperature=0.8)
    assert llm.ask("q") == ["a"] and llm.ask("q", temperature=0.5) == ["b"]
    assert all("temperature" not in s for s in client.seen) and client.seen[-1]["max_tokens"] == 16384


def test_llm_does_not_swallow_other_errors():
    class Broken(ScriptedClient):
        def create(self, **kwargs):
            raise RuntimeError("Error code: 401 - invalid api key")

    with pytest.raises(RuntimeError, match="401"):
        LLM(Broken([]), "m").ask("q")


def test_a_crashing_backend_becomes_an_error_the_model_sees():
    def boom(code):
        raise ZeroDivisionError("oops")

    client = ScriptedClient([("", [call("bad", code="x")]), ("", [call("finish", answer="?")])] * 2)
    ans = Agent(LLM(client, "m"), backends=[Fixed("bad", boom)], max_finish_rejections=0).solve("q")
    assert ans.steps[0].result.verdict is Verdict.ERROR and "crashed: ZeroDivisionError: oops" in ans.steps[0].result.output
    assert ans.answer == "?" and not ans.verified


def test_portfolio_survives_a_crashing_member():
    from formalkit import portfolio

    def boom(code):
        raise RuntimeError("member bug")

    p = portfolio(Fixed("bad", boom), Fixed("good", lambda code: (Verdict.UNSAT,)))
    assert p.run("x").verdict is Verdict.UNSAT
    both_bad = portfolio(Fixed("a", boom), Fixed("b", boom))
    r = both_bad.run("x")
    assert r.verdict is Verdict.ERROR and "member bug" in r.output


def test_a_hung_backend_is_unknown_not_error():
    import socket
    import threading

    listener = socket.socket()
    listener.bind(("127.0.0.1", 0))
    listener.listen(1)  # accepts the connection but never answers
    port = listener.getsockname()[1]
    held = []
    threading.Thread(target=lambda: held.append(listener.accept()), daemon=True).start()
    r = Remote("hung", f"http://127.0.0.1:{port}")
    result = r._post("/run", {"code": "x"}, timeout=-59.5)  # client waits timeout + 60 = 0.5 s
    assert result.verdict is Verdict.UNKNOWN and result.details["timeout"]
    listener.close()


def test_expert_iteration_survives_failed_attempts_and_stops_cleanly_on_budget():
    from formalkit.agent import Step
    from formalkit.core import Result
    from formalkit.learn import expert_iteration

    def flaky(statement):
        if statement == "boom":
            raise ConnectionError("api hiccup")
        return Step("b", {"code": statement}, Result(Verdict.PROVED))

    run = expert_iteration({"a": "ok", "b": "boom"}, flaky, rounds=1)
    assert set(run.dataset) == {"a"} and run.history[0]["errors"] == 1 and run.stopped is None

    b = Fixed("b", lambda code: (Verdict.UNKNOWN,))
    with observe(Budget(calls=1)):
        run = expert_iteration({"x": "1", "y": "2"}, lambda s: Step("b", {"code": s}, b.run(s)), rounds=3, workers=1)
    assert run.stopped and "budget exceeded" in run.stopped


def test_rollouts_and_evaluate_survive_individual_failures():
    from formalkit.agent import Step
    from formalkit.learn import evaluate, rollouts

    b = Fixed("b", lambda code: (Verdict.PROVED,))

    def turn(kwargs):
        if "bad" in kwargs["messages"][-1]["content"]:
            raise ConnectionError("api hiccup")
        return ("```\nok\n```", None)

    groups = rollouts(LLM(ScriptedClient([turn] * 4), "m"), b, ["good", "bad"], k=2)
    assert [[r.reward for r in g] for g in groups] == [[1.0, 1.0], [0.0, 0.0]]
    assert "api hiccup" in groups[1][0].result.output

    def solve(p):
        if p == "x":
            raise ValueError("solver bug")
        return Step("b", {"code": p}, b.run(p))

    report = evaluate({"1": "x", "2": "y"}, solve, judge=lambda p, s: True)
    assert report.correct == 1 and report.rows[0]["error"] == "ValueError: solver bug"


def test_pinned_backend_lets_an_agent_fill_only_the_hole():
    from formalkit.patterns import pinned

    lean = Fixed("lean", lambda code: (Verdict.PROVED,) if code == "theorem t : True := by\n  trivial" else (Verdict.ERROR,))
    p = pinned(lean, "theorem t : True := by\n  sorry")
    assert p.name == "lean_pinned" and "statement is fixed" in p.spec.guidance and p.tool_name == "lean_pinned"
    client = ScriptedClient([("", [call("lean_pinned", code="theorem other : True := trivial")]),
                             ("", [call("lean_pinned", code="trivial"), call("finish", answer="Proved")])])  # fmt: skip
    ans = Agent(LLM(client, "m"), backends=[p]).solve("Prove it.")
    assert [s.result.verdict for s in ans.steps] == [Verdict.ERROR, Verdict.PROVED] and ans.verified
    assert ans.steps[0].result.details["filled"].startswith("theorem t : True := by\n  theorem other")
    assert ans.recheck()


def test_mcp_offers_working_backends_when_one_fails_to_start(monkeypatch, capsys):
    import io
    import json

    from formalkit import mcp

    def fake_backend(name):
        if name == "broken":
            raise RuntimeError("image build failed")
        return Fixed(name, lambda code: (Verdict.SAT,))

    monkeypatch.setattr(mcp, "backend", fake_backend)
    monkeypatch.setattr("sys.stdin", io.StringIO(json.dumps({"jsonrpc": "2.0", "id": 1, "method": "tools/list"}) + "\n"))
    mcp.serve(["ok", "broken"])
    out, err = capsys.readouterr()
    assert [t["name"] for t in json.loads(out)["result"]["tools"]] == ["ok"] and "image build failed" in err


def test_build_continues_after_a_failure_and_reports_it(monkeypatch, capsys):
    from formalkit import cli

    built = []

    def fake_build(name, pull=False):
        if name == "cvc5":
            raise docker.DockerError("docker build -t failed:\nnetwork")
        built.append(name)

    monkeypatch.setattr(docker, "build", fake_build)
    monkeypatch.setattr(docker, "url", lambda name: None)
    with pytest.raises(SystemExit) as exit_info:
        cli.main(["build", "z3", "cvc5", "clingo"])
    assert built == ["z3", "clingo"] and "failed to build formalkit/cvc5" in str(exit_info.value.code)


def test_premises_consistency_per_backend():
    from formalkit import premises

    seen = []
    prolog = Fixed("prolog", lambda code: (seen.append(code) or Verdict.SAT,), language="Prolog", premise_check="?- true.")
    assert premises(prolog, "p(a).").consistent().verdict is Verdict.SAT and seen[-1].endswith("?- true.")
    idp = Fixed("idp", lambda code: (Verdict.SAT,), language="FO(.)")
    r = premises(idp, "theory T {}").consistent()
    assert r.verdict is Verdict.ERROR and "check=" in r.output
    assert premises(idp, "theory T {}", check="procedure main() {}").consistent().verdict is Verdict.SAT


def test_nonvacuous_rejects_results_the_backend_marks_vacuous():
    from formalkit import Rejected, nonvacuous
    from formalkit.agent import Step
    from formalkit.core import Result

    step = Step("vampire", {"code": "x"}, Result(Verdict.PROVED, details={"vacuous": True}))
    with pytest.raises(Rejected, match="contradictory"):
        nonvacuous()([step], None)


def test_refine_sends_multi_input_backends_a_json_object():
    from formalkit.patterns import refine

    got = []
    downward = Fixed("downward", lambda code: (Verdict.SAT,), inputs={"problem": "the problem", "mode": "m"},
                     optional=["mode"])  # fmt: skip
    downward.run = lambda code, timeout=30, **inputs: (got.append((code, inputs)), Fixed.run(downward, code))[1]
    client = ScriptedClient([('```json\n{"code": "(define (domain d))", "problem": "(define (problem p))"}\n```', None)])
    steps = refine(LLM(client, "m"), downward, "plan it", rounds=1)
    assert got == [("(define (domain d))", {"problem": "(define (problem p))"})]
    assert steps[0].arguments == {"code": "(define (domain d))", "problem": "(define (problem p))"}
    assert '"problem": the problem' in client.seen[0]["messages"][1]["content"]


def test_llm_drops_timeout_for_clients_without_it():
    class NoTimeout(ScriptedClient):
        def create(self, timeout=None, **kwargs):
            if timeout is not None:
                raise TypeError("create() got an unexpected keyword argument 'timeout'")
            return super().create(**kwargs)

    client = NoTimeout([("a", None), ("b", None)])
    llm = LLM(client, "m")
    assert llm.ask("q") == ["a"] and llm.ask("q") == ["b"] and "timeout" in llm._unsupported


def test_vacuity_check_understands_check_sat_assuming():
    from formalkit.evidence import drop_last_assert

    script = "(declare-const x Int)(assert (> x 5))(assert (> x 6))(check-sat-assuming ((not (> (* 2 x) 10))))"
    assert drop_last_assert(script) == "(declare-const x Int)(assert (> x 5))(assert (> x 6))(check-sat)"


def test_workdir_survives_lone_surrogates():
    from formalkit.server import workdir

    with workdir({"in.txt": "ok \ud800 ok"}) as d:
        assert (d / "in.txt").read_text() == "ok ? ok"


def test_grace_turn_accepts_only_finish():
    b = Fixed("b", lambda code: (Verdict.UNSAT,))
    client = ScriptedClient([("", [call("b", code="x")]),
                             ("", [call("b", code="again")]),           # grace turn: more tool calls are ignored
                             ("", [call("finish", answer="ok")])])  # fmt: skip
    ans = Agent(LLM(client, "m"), backends=[b], max_iterations=1).solve("q")
    assert b.runs == ["x"] and ans.answer is None  # the grace turn ran no tool and the model did not finish
    assert any("only finish is accepted" in str(m.get("content")) for m in ans.messages)
    fresh = Fixed("b", lambda code: (Verdict.UNSAT,))
    client = ScriptedClient([("", [call("b", code="x")]), ("", [call("b", code="y"), call("finish", answer="ok")])])
    ans = Agent(LLM(client, "m"), backends=[fresh], max_iterations=1).solve("q")
    assert ans.verified and ans.answer == "ok" and fresh.runs == ["x"]  # "y" was ignored, finish accepted


def test_llm_retries_once_when_the_budget_went_to_reasoning():
    class Thinker(ScriptedClient):
        def create(self, **kwargs):
            with self.lock:
                self.seen.append(kwargs)
                content = self.turns.pop(0)
            return {"choices": [{"message": {"content": content}, "finish_reason": "length" if not content else "stop"}],
                    "usage": {"total_tokens": 10}}

    client = Thinker(["", "the answer"])
    msg, usage = LLM(client, "m").complete([{"role": "user", "content": "q"}])
    assert msg["content"] == "the answer" and usage["total_tokens"] == 20 and len(client.seen) == 2


def test_agent_uses_each_backends_recommended_timeout():
    seen = []

    class Slow(Fixed):
        def call(self, arguments, timeout=30):
            seen.append(timeout)
            return super().call(arguments, timeout)

    slow = Slow("lean", lambda code: (Verdict.PROVED,), timeout=120)
    client = ScriptedClient([("", [call("lean", code="x"), call("finish", answer="ok")])] * 2)
    Agent(LLM(client, "m"), backends=[slow]).solve("q")
    Agent(LLM(client, "m"), backends=[slow], timeout=7).solve("q")
    assert seen == [120, 7]
