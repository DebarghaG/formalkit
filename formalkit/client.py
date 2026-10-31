"""Host side: backends, sessions, and the two ways to compose backends.

    >>> import formalkit
    >>> z3 = formalkit.backend("z3")          # starts the container if needed
    >>> z3.run("(declare-const x Int) (assert (> x 5)) (check-sat)").verdict
    <Verdict.SAT: 'sat'>

A :class:`Backend` is anything with a ``name``, a ``spec`` and a ``run``.
:class:`Remote` talks to a container; :func:`compiled` and :func:`portfolio`
wrap other backends and are backends themselves, so the agent, the MCP
server, the CLI and the patterns treat them all alike. Backends with
``spec.sessions`` also support step-by-step proving through :class:`State`.
"""

from __future__ import annotations

import importlib
import json
import re
import socket
import urllib.error
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, replace
from typing import Any, Callable, Sequence

from formalkit import docker
from formalkit.core import Result, Spec, Verdict
from formalkit.observe import Event, emit
from formalkit.registry import BACKENDS, VIRTUAL


class Backend:
    """The interface every backend shares. Subclass and implement ``spec`` and ``run``."""

    name: str

    @property
    def spec(self) -> Spec:
        """What this backend accepts, decides and returns."""
        raise NotImplementedError

    def run(self, code: str, timeout: float = 30, **inputs: str) -> Result:
        """Run ``code`` (plus named ``inputs``, see ``spec.inputs``) and return a Result.

        Must not raise for bad input or transport failures: those are ERROR
        results, so an LLM can read them and react.
        """
        raise NotImplementedError

    def start(self, code: str, timeout: float = 60) -> State:
        """Open a step-by-step session at the single hole in ``code``.

        Only backends with ``spec.sessions`` support this; the hole marker is
        backend-specific (``sorry`` for Lean).
        """
        raise NotImplementedError(f"{self.name} does not support sessions")

    def _step(self, state: str, step: str, timeout: float) -> Result:
        raise NotImplementedError(f"{self.name} does not support sessions")

    # -- LLM integration ---------------------------------------------------------

    def tool(self, style: str = "openai") -> dict[str, Any]:
        """This backend as an LLM tool definition.

        ``style`` is ``"openai"`` (chat-completions function tool),
        ``"anthropic"`` (Messages API tool) or ``"mcp"`` (MCP tool).
        """
        spec = self.spec
        properties = {"code": {"type": "string", "description": f"The {spec.language} input."}}
        for key, desc in spec.inputs.items():
            properties[key] = {"type": "string", "description": desc}
        required = ["code", *(k for k in spec.inputs if k not in spec.optional)]
        schema = {"type": "object", "properties": properties, "required": required}
        name, description = self.tool_name, spec.describe()
        if style == "openai":
            return {"type": "function", "function": {"name": name, "description": description, "parameters": schema}}
        if style == "anthropic":
            return {"name": name, "description": description, "input_schema": schema}
        if style == "mcp":
            return {"name": name, "description": description, "inputSchema": schema}
        raise ValueError(f"unknown tool style {style!r}")

    @property
    def tool_name(self) -> str:
        """``name`` made valid for LLM tool APIs (letters, digits, ``_``, ``-``; at most 64 characters)."""
        return re.sub(r"[^A-Za-z0-9_-]", "_", self.name)[:64] or "backend"

    def call(self, arguments: dict[str, Any] | str, timeout: float = 30) -> Result:
        """Run a tool call's arguments (dict or JSON string) - the tool() counterpart.

        Malformed calls - not a JSON object, no ``code``, unknown or missing
        inputs - come back as ERROR results that tell the model what to fix.
        """
        try:
            args = json.loads(arguments) if isinstance(arguments, str) else dict(arguments)
        except (TypeError, ValueError) as e:
            return Result(Verdict.ERROR, f"the tool arguments are not a JSON object: {e}", backend=self.name)
        if not isinstance(args, dict):
            return Result(Verdict.ERROR, "the tool arguments must be a JSON object", backend=self.name)
        code = args.pop("code", None)
        if not isinstance(code, str):
            what = "missing the required argument 'code'" if code is None else "'code' must be a string"
            return Result(Verdict.ERROR, f"{what}: the {self.spec.language} input.", backend=self.name)
        spec = self.spec
        unknown = sorted(set(args) - set(spec.inputs))
        missing = [k for k in spec.inputs if k not in spec.optional and args.get(k) in (None, "")]
        if unknown or missing:
            takes = ", ".join(["code", *spec.inputs])
            problem = f"unknown argument(s) {unknown}" if unknown else f"missing required argument(s) {missing}"
            return Result(Verdict.ERROR, f"{problem}; this tool takes: {takes}.", backend=self.name)
        return self.run(code, timeout=timeout, **{k: str(v) for k, v in args.items() if v is not None})

    def __repr__(self) -> str:
        return f"<{type(self).__name__} {self.name}>"


@dataclass(frozen=True)
class State:
    """A point in a step-by-step session: the Result that produced it plus the path to it.

    States are immutable values, so search can branch freely::

        root = lean.start("theorem t (n : Nat) : n + 0 = n := by sorry")
        root.goals                    # ['n : Nat\\n⊢ n + 0 = n']
        done = root.apply("simp")     # a new State; root is unchanged
        done.solved, done.proof       # True, the full checked proof text
    """

    backend: Backend
    result: Result
    path: tuple[str, ...] = ()

    @property
    def id(self) -> str | None:
        return self.result.details.get("state")

    @property
    def goals(self) -> list[str]:
        return self.result.goals

    @property
    def solved(self) -> bool:
        """All goals closed and the assembled proof checked by the backend."""
        return self.result.verdict is Verdict.PROVED

    @property
    def failed(self) -> bool:
        return self.result.verdict is Verdict.ERROR

    @property
    def proof(self) -> Any:
        return self.result.proof

    def apply(self, step: str, timeout: float = 60) -> State:
        """Apply one step (e.g. a tactic). A failed step yields a failed State, not an exception."""
        if self.id is None:
            raise ValueError("this state is solved or failed; step from an open state")
        return State(self.backend, self.backend._step(self.id, step, timeout), self.path + (step,))


class Remote(Backend):
    """A backend served over HTTP, usually by its own Docker container."""

    def __init__(self, name: str, url: str, managed: bool = False) -> None:
        self.name = name
        self.url = url.rstrip("/")
        self.managed = managed  # started through Docker by formalkit: restartable
        self._spec: Spec | None = None

    def __repr__(self) -> str:
        return f"<Remote {self.name} {self.url}>"

    def _request(self, path: str, payload: dict | None = None, timeout: float = 30) -> dict:
        data = json.dumps(payload).encode() if payload is not None else None
        req = urllib.request.Request(self.url + path, data=data, headers={"Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return json.loads(resp.read())
        except urllib.error.HTTPError as e:
            if e.code == 501:
                raise NotImplementedError(f"{self.name} does not support sessions") from None
            raise RuntimeError(f"{self.name}: HTTP {e.code}: {e.read().decode(errors='replace')}") from None

    def _post(self, path: str, payload: dict, timeout: float) -> Result:
        body = {**payload, "timeout": timeout}
        try:
            return Result.from_dict(self._request(path, body, timeout=timeout + 60))
        except RuntimeError as e:  # the server answered, but rejected the request
            return Result(Verdict.ERROR, f"backend {self.name!r} rejected the request: {e}", backend=self.name)
        except OSError as e:
            if isinstance(getattr(e, "reason", e), (TimeoutError, socket.timeout)):  # hung past its own limit
                return Result(Verdict.UNKNOWN, f"{self.name} gave no answer within {timeout + 60:.0f}s",
                              {"timeout": True}, backend=self.name)  # fmt: skip
            if not (self.managed and path == "/run" and _connection_lost(e)):
                return Result(Verdict.ERROR, f"could not reach backend {self.name!r}: {e}", backend=self.name)
        # The container is gone (crashed, killed, out of memory): restart it and retry once.
        # Only whole runs are retried; session states died with the container.
        try:
            self.url = docker.up(self.name).rstrip("/")
            return Result.from_dict(self._request(path, body, timeout=timeout + 60))
        except (OSError, RuntimeError, docker.DockerError) as e:
            return Result(Verdict.ERROR, f"backend {self.name!r} died and could not be restarted: {e}", backend=self.name)

    @property
    def spec(self) -> Spec:
        if self._spec is None:
            self._spec = Spec.from_dict(self._request("/spec"))
        return self._spec

    def run(self, code: str, timeout: float = 30, **inputs: str) -> Result:
        result = self._post("/run", {"code": code, "inputs": inputs}, timeout)
        emit(Event("run", self.name, code, result))
        return result

    def start(self, code: str, timeout: float = 60) -> State:
        if not self.spec.sessions:
            raise NotImplementedError(f"{self.name} does not support sessions")
        result = self._post("/start", {"code": code}, timeout)
        emit(Event("start", self.name, code, result))
        return State(self, result)

    def _step(self, state: str, step: str, timeout: float) -> Result:
        result = self._post("/step", {"state": state, "step": step}, timeout)
        emit(Event("step", self.name, step, result, parent=state))
        return result

    def stop(self) -> None:
        """Stop this backend's container (other users of it lose it too)."""
        docker.down(self.name)


def _connection_lost(e: Exception) -> bool:
    """True for a refused or reset connection - not for a slow run that timed out."""
    reason = getattr(e, "reason", e)
    return isinstance(reason, ConnectionError) and not isinstance(reason, (TimeoutError, socket.timeout))


# -- composition --------------------------------------------------------------------


class Compiled(Backend):
    """A backend that accepts an intermediate representation and compiles it for another."""

    def __init__(self, inner: Backend, compile: Callable[[str], str], spec: Spec) -> None:
        self.inner, self.compile, self.name, self._spec = inner, compile, spec.name, spec

    @property
    def spec(self) -> Spec:
        return self._spec

    def run(self, code: str, timeout: float = 30, **inputs: str) -> Result:
        try:
            target = self.compile(code)
        except Exception as e:  # compile errors are feedback, like any other error
            return Result(Verdict.ERROR, f"{self.spec.language} error: {e}", {"via": self.inner.name}, self.name)
        result = self.inner.run(target, timeout, **inputs)
        result.details.update(compiled=target, via=self.inner.name)
        result.backend = self.name
        if result.verdict is Verdict.ERROR:
            numbered = "\n".join(f"{i:4} | {line}" for i, line in enumerate(target.splitlines(), 1))
            result.output = f"{result.output}\n\nThe {self.inner.spec.language} compiled from your input:\n{numbered}"
        return result


def compiled(
    inner: Backend,
    compile: Callable[[str], str],
    *,
    name: str,
    language: str,
    emits: str,
    guidance: str = "",
    example: str = "",
) -> Compiled:
    """Expose ``inner`` through an intermediate representation.

    ``compile`` turns the IR into ``inner``'s language and raises on invalid
    input; its message becomes the ERROR feedback the model sees. The
    result is a Backend, usable anywhere a backend is.
    """
    spec = replace(
        inner.spec,
        name=name,
        family=f"{inner.spec.family} via IR",
        language=language,
        emits=emits,
        feedback=f"{inner.spec.feedback} The compiled {inner.spec.language} is in details['compiled'].",
        guidance=guidance,
        example=example,
        sessions=False,
    )
    return Compiled(inner, compile, spec)


class Premises(Compiled):
    """A backend with fixed premises: formalize a theory once, then query it many times."""

    def __init__(self, inner: Backend, premises: str, spec: Spec, check: str | None) -> None:
        super().__init__(inner, lambda query: f"{premises.rstrip()}\n\n{query}", spec)
        self.premises, self._check = premises, check

    def consistent(self, timeout: float = 30) -> Result:
        """Run the premises alone: sat means consistent; unsat means every query would be
        vacuously answered (the ``core`` detail, when the backend reports one, shows why)."""
        if self._check is None:
            return Result(Verdict.ERROR, f"{self.inner.name} has no generic way to check premises alone; pass "
                          "premises(..., check=<what to append to run them>)", backend=self.inner.name)  # fmt: skip
        return self.inner.run(f"{self.premises.rstrip()}\n{self._check}", timeout)


def premises(inner: Backend, text: str, *, name: str | None = None, check: str | None = None) -> Premises:
    """``inner`` with ``text`` prepended to every input.

    Each query then only states what it asks, e.g. ``kb.run("(assert (not
    claim)) (check-sat)")`` against an SMT theory, or a query block against an
    FO(.) knowledge base. ``check`` is what ``consistent()`` appends to run
    the premises alone (default: the backend's ``spec.premise_check``, or
    ``(check-sat)`` for SMT-LIB).
    """
    if check is None:
        check = inner.spec.premise_check or ("(check-sat)" if inner.spec.language.startswith("SMT-LIB") else None)
    spec = replace(
        inner.spec,
        name=name or f"{inner.name}_premises",
        family=f"{inner.spec.family} with premises",
        guidance=f"{inner.spec.guidance}\n\nThese premises are already loaded; send only the query:\n{text.strip()}",
        sessions=False,
    )
    return Premises(inner, text, spec, check)


class Portfolio(Backend):
    """Run the same input on several backends at once; the first decisive verdict wins."""

    def __init__(self, members: Sequence[Backend], name: str | None = None) -> None:
        if len(members) < 2:
            raise ValueError("a portfolio needs at least two backends")
        languages = {m.spec.language for m in members}
        if len(languages) > 1:
            raise ValueError(f"portfolio members must share one input language, got {sorted(languages)}")
        self.members = list(members)
        self.name = name or "_".join(m.name for m in members)
        first = members[0].spec
        self._spec = replace(
            first,
            name=self.name,
            family="Portfolio",
            authority=" / ".join(f"{m.name}: {m.spec.authority}" for m in members),
            feedback=f"the first decisive member's result; details['portfolio'] lists every member's verdict. {first.feedback}",
            guidance="\n\n".join(
                [f"Your input runs on {', '.join(m.name for m in members)} in parallel; the first decisive verdict wins."]
                + [f"[{m.name}] {m.spec.guidance}" for m in members if m.spec.guidance]
            ),
            sessions=False,
        )

    @property
    def spec(self) -> Spec:
        return self._spec

    def run(self, code: str, timeout: float = 30, **inputs: str) -> Result:
        pool = ThreadPoolExecutor(len(self.members))
        futures = [pool.submit(_safe_run, m, code, timeout, inputs) for m in self.members]
        done: list[Result] = []
        try:
            for future in as_completed(futures):
                done.append(future.result())
                if done[-1].decisive:
                    break
        finally:
            pool.shutdown(wait=False, cancel_futures=True)
        verdicts = {r.backend: r.verdict.value for r in done}
        winner = done[-1] if done[-1].decisive else None
        if winner is None:  # nobody decided: report everything, unknown beats error
            verdict = Verdict.UNKNOWN if any(r.verdict is Verdict.UNKNOWN for r in done) else Verdict.ERROR
            output = "\n\n".join(f"[{r.backend}] {r.feedback()}" for r in done)
            return Result(verdict, output, {"portfolio": verdicts}, self.name, max(r.elapsed for r in done))
        winner.details["portfolio"] = verdicts
        return winner


def _safe_run(b: Backend, code: str, timeout: float, inputs: dict) -> Result:
    """``b.run``, with a crash turned into an ERROR result (one bad member must not sink the race)."""
    try:
        return b.run(code, timeout, **inputs)
    except Exception as e:
        return Result(Verdict.ERROR, f"{b.name} crashed: {type(e).__name__}: {e}", backend=b.name)


def portfolio(*members: Backend, name: str | None = None) -> Portfolio:
    """Race backends that read the same language, e.g. ``portfolio(z3, cvc5)``
    or a prover against a model finder, ``portfolio(prover9, mace4)``."""
    return Portfolio(members, name)


# -- lookup -------------------------------------------------------------------------


def backend(name: str, url: str | None = None) -> Backend:
    """Get a backend by name, starting its container if it is not running.

    Pass ``url`` to attach to a backend served elsewhere (another host, a
    compose stack, a Kubernetes service) without touching Docker. Virtual
    backends (e.g. ``pot``, compiled to z3) are built from their parts.
    """
    if url is None and name not in VIRTUAL and name not in BACKENDS:
        raise KeyError(f"unknown backend {name!r}; known: {', '.join([*BACKENDS, *VIRTUAL])}")
    if name in VIRTUAL and url is None:
        module, _, attr = VIRTUAL[name].factory.partition(":")
        return getattr(importlib.import_module(module), attr)()
    if url is not None:
        return Remote(name, url)
    return Remote(name, docker.up(name), managed=True)


def backends(*names: str) -> list[Backend]:
    """Several backends at once: ``z3, clingo = formalkit.backends("z3", "clingo")``."""
    return [backend(n) for n in names]
