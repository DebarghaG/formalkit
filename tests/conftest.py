"""Shared fakes: a scripted OpenAI-style client and in-process toy backends."""

from __future__ import annotations

import json
import os
import threading
from types import SimpleNamespace

from formalkit import Backend, Result, Spec, State, Verdict, docker
from formalkit.observe import Event, emit

_running_at_start: set[str] | None = None


def pytest_sessionstart(session):
    """Remember which backends were already running, so we leave them alone."""
    global _running_at_start
    try:
        _running_at_start = set(docker.running())
    except docker.DockerError:  # no Docker: only the non-Docker tests can run anyway
        _running_at_start = None


def pytest_sessionfinish(session, exitstatus):
    """Stop the backends this test run started - once, at the end, so they stay warm across modules.

    Set FORMALKIT_KEEP=1 to leave them running (e.g. when several test runs share backends).
    """
    if _running_at_start is not None and not os.environ.get("FORMALKIT_KEEP"):
        for name in set(docker.running()) - _running_at_start:
            docker.down(name)


def call(name, **args):
    """An OpenAI-style tool call."""
    return {"id": f"c{name}{len(args)}", "type": "function", "function": {"name": name, "arguments": json.dumps(args)}}


class ScriptedClient:
    """An OpenAI-compatible client that replays assistant turns.

    Each turn is ``(content, tool_calls)``, or a callable taking the request
    kwargs and returning one (for replies that depend on the prompt).
    """

    def __init__(self, turns):
        self.turns, self.seen = list(turns), []
        self.lock = threading.Lock()
        self.chat = SimpleNamespace(completions=SimpleNamespace(create=self.create))

    def create(self, **kwargs):
        with self.lock:
            self.seen.append(kwargs)
            turn = self.turns.pop(0)
        content, calls = turn(kwargs) if callable(turn) else turn
        msg = {"role": "assistant", "content": content, "tool_calls": calls}
        return {"choices": [{"message": msg}], "usage": {"total_tokens": 10}}


def spec(name, language="toy", **kw):
    fields = dict(family="Test", emits="e", authority="a", feedback="f", use="u", guidance="g")
    return Spec(name=name, language=language, **{**fields, **kw})


class Fixed(Backend):
    """Answers with a function of the code; counts runs."""

    def __init__(self, name, fn, language="toy", **kw):
        self.name, self.fn, self.runs = name, fn, []
        self._spec = spec(name, language, **kw)

    @property
    def spec(self):
        return self._spec

    def run(self, code, timeout=30, **inputs):
        self.runs.append(code)
        verdict, *rest = self.fn(code)
        result = Result(verdict, rest[0] if rest else code, rest[1] if len(rest) > 1 else {}, self.name)
        emit(Event("run", self.name, code, result))  # a backend that executes something reports it
        return result


class Countdown(Backend):
    """A session backend: the goal is a number; steps subtract from it; 0 is proved.

    ``start("n")`` opens a session with goal n; ``apply("k")`` subtracts k
    (k must be 1..3, else error). Reaching exactly 0 solves it.
    """

    name = "countdown"

    def __init__(self):
        self.states, self.calls = {}, 0

    @property
    def spec(self):
        return spec("countdown", sessions=True)

    def run(self, code, timeout=30, **inputs):
        return Result(Verdict.PROVED if code.strip() == "0" else Verdict.UNKNOWN, code, {}, self.name)

    def _open(self, n):
        sid = str(len(self.states))
        self.states[sid] = n
        return Result(Verdict.UNKNOWN, f"goal {n}", {"state": sid, "goals": [f"reach 0 from {n}"]}, self.name)

    def start(self, code, timeout=60):
        result = self._open(int(code))
        emit(Event("start", self.name, code, result))
        return State(self, result)

    def _step(self, state, step, timeout):
        self.calls += 1
        k = int(step) if step.isdigit() else 0
        if not 1 <= k <= 3 or self.states[state] - k < 0:
            result = Result(Verdict.ERROR, f"bad step {step}", {}, self.name)
        elif self.states[state] == k:
            result = Result(Verdict.PROVED, "done", {"proof": "steps"}, self.name)
        else:
            result = self._open(self.states[state] - k)
        emit(Event("step", self.name, step, result, parent=state))
        return result
