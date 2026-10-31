"""The agent loop: an LLM uses formal backends as an iterative scratchpad.

This generalizes ProofOfThought's agentic SMT-LIB loop from Z3 to any set of
backends:

    1. the model writes a program and calls a backend tool,
    2. reads the verdict and feedback (errors, models, goals, traces),
    3. repairs or strengthens the program and calls again,
    4. ends with ``finish(answer, evidence=[run numbers])``.

``finish`` is not taken at face value: an evidence policy (see
:mod:`formalkit.evidence`) decides which runs back the answer and rejects
weak ones, up to ``max_finish_rejections`` times; after that the answer is
accepted with ``verified=False``. So ``answer.verified`` always means
"backed by decisive verdicts", ``answer.evidence`` holds those runs, and
``answer.recheck()`` reproduces them.

The loop's behavior is adjustable through four hooks, all plain callables:
``evidence`` (what counts as backing), ``render`` (how a Result is shown to
the model), ``nudge`` (what to say after a turn without a tool call) and
``on_step`` (observe every run, e.g. to log trajectories).

Under a :class:`~formalkit.Budget`, an exhausted budget ends the loop
cleanly: the partial Answer is returned with ``error`` set and its
trajectory intact.
"""

from __future__ import annotations

import json
import re
import uuid
from dataclasses import dataclass, field
from typing import Any, Callable, Sequence

from formalkit.client import Backend, backend
from formalkit.core import Result, Verdict
from formalkit.evidence import Policy, Rejected, cited_or_last
from formalkit.llm import LLM
from formalkit.observe import BudgetExceeded

FINISH_TOOL = {
    "type": "function",
    "function": {
        "name": "finish",
        "description": (
            "End the task with your final answer. Only call this after tool runs have decisively "
            "confirmed the answer; unverified finishes are rejected."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "answer": {"type": "string", "description": "The final answer value only, e.g. 'Yes', 'B', '42'."},
                "evidence": {
                    "type": "array",
                    "items": {"type": "integer"},
                    "description": "Numbers of the runs (run #n) that establish the answer. Defaults to your last run.",
                },
                "explanation": {"type": "string", "description": "One or two sentences on how it was verified."},
            },
            "required": ["answer"],
        },
    },
}

SYSTEM_PROMPT = """You solve problems by writing formal programs and checking them with formal tools. The tools are your scratchpad: their verdicts are authoritative, your own reasoning is not.

Workflow:
1. Briefly analyze the problem and pick the most suitable tool.
2. Encode the problem completely and faithfully, and call the tool.
3. Read the verdict and feedback. On an error, fix the program; on an inconclusive or unexpected result, revise the encoding. Call again as often as needed.
4. Once decisive verdicts back your answer, call finish with only the answer value, citing the run numbers that establish it.

Every tool returns one verdict: proved, refuted, sat, unsat, optimal, unknown, or error.
To establish a claim with a satisfiability tool, assert the premises and, as the LAST assertion, the NEGATION of the claim - in SMT-LIB name it: (assert (! (not claim) :named goal)) - then unsat proves the claim and sat yields a counterexample.
An answer may need several runs, e.g. "the minimum is 3" needs 3 to be feasible (sat) and 2 to be infeasible (unsat); cite all of them.
A finish call is rejected unless the cited runs (by default your most recent run) are decisive.

Available tools:
"""


@dataclass
class Step:
    """One backend run: which backend, with what arguments, and what it returned.

    ``ref`` is the Backend object that ran it (not serialized); it lets the
    run be reproduced even for virtual backends like portfolios.
    """

    backend: str
    arguments: dict[str, Any]
    result: Result
    ref: Backend | None = field(default=None, repr=False, compare=False)

    def rerun(self, timeout: float = 60) -> Result:
        """Run this step's input again (bookkeeping keys such as ``fill`` are not inputs)."""
        b = self.ref or backend(self.backend)
        accepted = {"code", *b.spec.inputs}
        return b.call({k: v for k, v in self.arguments.items() if k in accepted}, timeout=timeout)

    def to_dict(self) -> dict[str, Any]:
        return {"backend": self.backend, "arguments": self.arguments, "result": self.result.to_dict()}


@dataclass
class Answer:
    """The outcome of :meth:`Agent.solve` - the answer plus its full audit trail."""

    question: str
    answer: str | None = None
    explanation: str | None = None
    verified: bool = False
    evidence: list[Step] = field(default_factory=list)  # the decisive runs that back the answer
    steps: list[Step] = field(default_factory=list)  # every run, in order (run #n is steps[n-1])
    messages: list[dict[str, Any]] = field(default_factory=list)
    iterations: int = 0
    usage: dict[str, int] = field(default_factory=dict)  # tokens spent on this answer
    blocked: list[dict[str, Any]] = field(default_factory=list)  # tool calls the guard refused
    error: str | None = None

    @property
    def verdict(self) -> Verdict | None:
        """The verdict of the last backing run (None when unverified)."""
        return self.evidence[-1].result.verdict if self.evidence else None

    def recheck(self, timeout: float = 60) -> bool:
        """Re-run every backing run and confirm each still gives the same verdict."""
        return bool(self.evidence) and all(s.rerun(timeout).verdict is s.result.verdict for s in self.evidence)

    def __str__(self) -> str:
        if self.answer is None:
            return f"no answer ({self.error or self.explanation or 'no finish'})"
        how = ", ".join(f"{s.backend}: {s.result.verdict}" for s in self.evidence) or "unverified"
        return f"{self.answer}  [{how}]"

    def to_dict(self) -> dict[str, Any]:
        return {
            "question": self.question,
            "answer": self.answer,
            "explanation": self.explanation,
            "verified": self.verified,
            "evidence": [s.to_dict() for s in self.evidence],
            "steps": [s.to_dict() for s in self.steps],
            "iterations": self.iterations,
            "usage": self.usage,
            "blocked": self.blocked,
            "error": self.error,
        }


def default_nudge(steps: Sequence[Step]) -> str:
    """What to tell a model that ended its turn without calling a tool."""
    if not steps:
        return "You did not call a tool. Encode the problem and call one of the tools now."
    last = steps[-1].result
    if last.verdict is Verdict.ERROR:
        return "The last tool run failed with an error. Fix the program and call the tool again."
    if last.decisive:
        return (
            f"Run #{len(steps)} was decisive ({last.verdict}). If the runs so far settle the question, "
            "call finish now, citing them; otherwise continue verifying."
        )
    return "The last run was inconclusive. Revise the encoding (simplify, add bounds, or try another tool) and call again."


class Agent:
    """Let an LLM solve problems with formal backends.

    Args:
        llm: an :class:`~formalkit.LLM`, or an OpenAI-compatible client
            together with ``model`` (extra keyword arguments configure it).
        backends: backend names or Backend objects to expose as tools.
        max_iterations: model turns before giving up.
        max_finish_rejections: rejected finishes before one is accepted
            with ``verified=False``.
        max_nudges: consecutive turns without a tool call that get a nudge.
        timeout: per-run backend timeout in seconds (default: each backend's
            recommended ``spec.timeout``, e.g. longer for Lean with Mathlib).
        system_prompt: replaces the default workflow preamble (tool
            descriptions are always appended).
        evidence: policy deciding which runs back an answer
            (default :func:`~formalkit.evidence.cited_or_last`).
        render: how a Result is shown to the model (default ``Result.feedback``).
        nudge: message after a turn without a tool call (default :func:`default_nudge`).
        on_step: called with every new Step, e.g. to log trajectories.
        guard: called with each proposed tool call ``(name, arguments)``
            *before* it runs; returns None to allow it or a reason to block
            it (e.g. a :class:`~formalkit.Guard` over a formal policy).
            Blocked calls are shown to the model and kept in ``answer.blocked``.
    """

    def __init__(
        self,
        llm: LLM | Any,
        model: str | None = None,
        backends: Sequence[str | Backend] = ("z3",),
        *,
        max_iterations: int = 10,
        max_finish_rejections: int = 2,
        max_nudges: int = 2,
        timeout: float | None = None,
        system_prompt: str | None = None,
        evidence: Policy = cited_or_last,
        render: Callable[[Result], str] = Result.feedback,
        nudge: Callable[[Sequence[Step]], str] = default_nudge,
        on_step: Callable[[Step], None] | None = None,
        guard: Callable[[str, dict[str, Any]], str | None] | None = None,
        **llm_options: Any,
    ) -> None:
        if not isinstance(llm, LLM):
            if model is None:
                raise TypeError("pass a formalkit.LLM, or a client together with model=...")
            llm = LLM(llm, model, **llm_options)
        self.llm = llm
        # Keyed by tool name: the name the model calls, valid for every tool API.
        self.backends = {b.tool_name: b for b in (x if isinstance(x, Backend) else backend(x) for x in backends)}
        self.max_iterations = max_iterations
        self.max_finish_rejections = max_finish_rejections
        self.max_nudges = max_nudges
        self.timeout = timeout
        self.evidence, self.render, self.nudge, self.on_step, self.guard = evidence, render, nudge, on_step, guard
        self.tools = [b.tool("openai") for b in self.backends.values()] + [FINISH_TOOL]
        listing = "\n".join(f"- {name}: {b.spec.language} ({b.spec.use})" for name, b in self.backends.items())
        self.system_prompt = (system_prompt or SYSTEM_PROMPT) + listing

    def solve(self, question: str, answer_format: str | None = None) -> Answer:
        """Run the loop on one question. ``answer_format`` is appended to it,
        e.g. ``"Answer Yes or No."`` or the multiple-choice options."""
        ans = Answer(question=question)
        messages: list[dict[str, Any]] = [
            {"role": "system", "content": self.system_prompt},
            {"role": "user", "content": question + (f"\n\n{answer_format}" if answer_format else "")},
        ]
        nudges = rejections = 0
        limit, grace, finish_only = self.max_iterations, True, False
        try:
            while ans.iterations < limit:
                ans.iterations += 1
                last_turn = ans.iterations == limit
                try:
                    msg, usage = self.llm.complete(messages, tools=self.tools)
                    for key, value in usage.items():
                        ans.usage[key] = ans.usage.get(key, 0) + value
                except BudgetExceeded:
                    raise
                except Exception as e:  # transport failure: keep the trajectory
                    ans.error = f"LLM call failed: {e}"
                    break
                if not msg.get("tool_calls"):
                    # Local servers often leave textual tool calls unparsed; recover them.
                    recovered = parse_tool_calls(msg["content"])
                    if recovered:
                        msg["tool_calls"] = recovered
                calls = msg.get("tool_calls") or []
                messages.append(msg)
                if not calls:
                    if nudges >= self.max_nudges or last_turn:
                        break
                    nudges += 1
                    messages.append({"role": "user", "content": self.nudge(ans.steps)})
                    continue
                nudges = 0
                allow_unverified = rejections >= self.max_finish_rejections or last_turn
                # Tool runs first, so a same-turn verdict can back the finish.
                for call in sorted(calls, key=lambda c: _name(c) == "finish"):
                    if ans.answer is not None:  # every tool call still needs a reply
                        messages.append(_reply(call, "ignored: already finished"))
                    elif finish_only and _name(call) != "finish":
                        messages.append(_reply(call, "IGNORED: no tool runs are left; only finish is accepted now."))
                    elif _name(call) == "finish":
                        rejections += not self._finish(call, ans, messages, allow_unverified)
                    else:
                        self._run_tool(call, ans, messages)
                if ans.answer is not None:
                    break
                # A decisive verdict on the final turn earns one extra turn - for
                # finish only - so a proof isn't wasted for lack of a finish call.
                if last_turn and grace and ans.steps and ans.steps[-1].result.decisive:
                    limit, grace, finish_only = limit + 1, False, True
                    messages.append({"role": "user", "content": (
                        f"You are out of tool runs. Run #{len(ans.steps)} was decisive ({ans.steps[-1].result.verdict}). "
                        "Call finish now with your answer, citing the runs that establish it.")})  # fmt: skip
        except BudgetExceeded as e:  # out of calls/tokens/time: return what we have
            ans.error = str(e)
        if ans.answer is None and ans.error is None:
            ans.explanation = "no finish call within max_iterations"
        ans.messages = messages
        return ans

    # -- internals -----------------------------------------------------------------

    def _run_tool(self, call: dict[str, Any], ans: Answer, messages: list[dict[str, Any]]) -> None:
        name, args = _name(call), _arguments(call)
        if name not in self.backends:
            content = f"unknown tool {name!r}; available: {', '.join(self.backends)}, finish"
        elif args is None:
            content = "error: tool arguments were not valid JSON; call the tool again."
        elif self.guard is not None and (reason := self._guard(name, args)) is not None:
            ans.blocked.append({"tool": name, "arguments": args, "reason": reason})
            content = f"BLOCKED by policy: {reason}. This call was not executed."
        else:
            b = self.backends[name]
            try:
                result = b.call(args, timeout=self.timeout or b.spec.timeout)
            except BudgetExceeded:
                raise
            except Exception as e:  # a buggy backend must not take the whole trajectory down
                result = Result(Verdict.ERROR, f"the {b.name} backend crashed: {type(e).__name__}: {e}", backend=b.name)
            step = Step(b.name, args, result, b)
            ans.steps.append(step)
            if self.on_step:
                self.on_step(step)
            content = f"run #{len(ans.steps)}\n{self.render(step.result)}"
        messages.append(_reply(call, content))

    def _guard(self, name: str, args: dict[str, Any]) -> str | None:
        try:
            return self.guard(name, args)
        except BudgetExceeded:
            raise
        except Exception as e:  # a broken guard must not wave calls through
            return f"the guard failed ({type(e).__name__}: {e}); blocked to be safe"

    def _finish(self, call: dict[str, Any], ans: Answer, messages: list[dict[str, Any]], allow_unverified: bool) -> bool:
        """Accept (True) or reject (False) a finish call."""
        args = _arguments(call)
        if args is None or "answer" not in args:
            messages.append(_reply(call, "error: finish needs JSON arguments with an 'answer' field."))
            return False
        try:
            evidence = self.evidence(ans.steps, _run_numbers(args.get("evidence")))
        except Rejected as reason:
            if not allow_unverified:
                messages.append(_reply(call, f"REJECTED: {reason}"))
                return False
            evidence = []
        ans.answer = str(args["answer"]).strip()
        ans.explanation = args.get("explanation")
        ans.evidence, ans.verified = evidence, bool(evidence)
        messages.append(_reply(call, "finished"))
        return True


# -- helpers ------------------------------------------------------------------------

_TOOL_CALL_RE = re.compile(r"<tool_call>\s*(.*?)\s*</tool_call>", re.DOTALL)
_QWEN_FN_RE = re.compile(r"<function=([\w-]+)>(.*?)</function>", re.DOTALL)
_QWEN_PARAM_RE = re.compile(r"<parameter=([\w-]+)>\s*(.*?)\s*</parameter>", re.DOTALL)


def parse_tool_calls(content: str) -> list[dict[str, Any]]:
    """Recover textual tool calls (hermes JSON or qwen XML) from message content."""
    calls = []
    for body in _TOOL_CALL_RE.findall(content or ""):
        try:
            obj = json.loads(body)
            calls.append((obj["name"], obj.get("arguments") or obj.get("parameters") or {}))
            continue
        except (ValueError, KeyError, TypeError):
            pass
        for name, inner in _QWEN_FN_RE.findall(body):
            calls.append((name, dict(_QWEN_PARAM_RE.findall(inner))))
    return [
        {"id": f"call_{uuid.uuid4().hex[:8]}", "type": "function", "function": {"name": n, "arguments": json.dumps(a)}}
        for n, a in calls
    ]


def _reply(call: dict[str, Any], content: str) -> dict[str, Any]:
    return {"role": "tool", "tool_call_id": call.get("id", ""), "content": content}


def _name(call: dict[str, Any]) -> str:
    return (call.get("function") or {}).get("name") or ""


def _arguments(call: dict[str, Any]) -> dict[str, Any] | None:
    raw = (call.get("function") or {}).get("arguments")
    if isinstance(raw, dict):
        return raw
    try:
        parsed = json.loads(raw or "{}")
    except (TypeError, ValueError):
        return None
    return parsed if isinstance(parsed, dict) else None


def _run_numbers(value: Any) -> list[int] | None:
    """Cited run numbers from a finish call, tolerating 3, "#3", "2, 3" and [2, 3]."""
    if value in (None, "", []):
        return None
    items = value if isinstance(value, list) else re.findall(r"\d+", str(value))
    numbers = []
    for item in items:
        try:
            numbers.append(int(str(item).lstrip("#")))
        except ValueError:
            continue
    return numbers or None
