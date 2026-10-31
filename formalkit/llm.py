"""The one LLM abstraction: a thin wrapper over any OpenAI-compatible client.

    llm = formalkit.LLM(OpenAI(), "gpt-5")
    llm.ask("Write an SMT-LIB script that ...")          # -> ["..."]
    llm.ask(prompt, n=8, temperature=1.0)                 # 8 samples, in parallel
    llm.chat(messages, tools=[...])                       # one raw turn

The agent and every pattern talk to models only through this class, so
swapping providers (OpenAI, Azure, DeepSeek, vLLM, sglang, Ollama, LiteLLM,
Anthropic's OpenAI-compatible endpoint) never touches them.
"""

from __future__ import annotations

import re
import threading
from concurrent.futures import ThreadPoolExecutor
from typing import Any

from formalkit.observe import Event, emit

_FENCE_RE = re.compile(r"```[^\n`]*\n(.*?)```", re.DOTALL)


def extract_code(text: str) -> str:
    """The last fenced code block in ``text``, or the whole text if there is none."""
    blocks = _FENCE_RE.findall(text or "")
    return (blocks[-1] if blocks else text or "").strip()


class LLM:
    """An OpenAI-compatible chat client plus sampling defaults and a usage tally."""

    def __init__(
        self,
        client: Any,
        model: str,
        *,
        temperature: float | None = None,
        max_tokens: int | None = 16384,
        timeout: float | None = 600,
        **extra: Any,
    ) -> None:
        self.client = client
        self.model = model
        self.temperature = temperature  # None: don't send (some models only allow the default)
        self.max_tokens = max_tokens
        self.timeout = timeout  # per request, seconds: a hung API call must not block a run forever
        self.extra = extra  # passed through to every request, e.g. reasoning_effort="low"
        self.usage: dict[str, int] = {}
        self._tokens_param: str | None = None  # learned on first call
        self._unsupported: set[str] = set()  # request fields the server rejected
        self._lock = threading.Lock()

    def __repr__(self) -> str:
        return f"LLM({self.model!r})"

    def chat(self, messages: list[dict[str, Any]], tools: list[dict] | None = None, **overrides: Any) -> dict[str, Any]:
        """One completion. Returns the assistant message as a plain dict
        (``role``, ``content``, and ``tool_calls`` when there are any)."""
        return self.complete(messages, tools, **overrides)[0]

    def complete(
        self, messages: list[dict[str, Any]], tools: list[dict] | None = None, **overrides: Any
    ) -> tuple[dict[str, Any], dict[str, int]]:
        """Like :meth:`chat`, plus this call's token usage (safe when calls run concurrently)."""
        kwargs: dict[str, Any] = {"model": self.model, "messages": messages, **self.extra}
        if tools:
            kwargs["tools"] = tools
        temperature = overrides.pop("temperature", self.temperature)
        if temperature is not None:
            kwargs["temperature"] = temperature
        kwargs.update(overrides)
        total: dict[str, int] = {}
        for _ in range(2):
            response = _plain(self._create(kwargs))
            usage = {k: v for k, v in (response.get("usage") or {}).items() if isinstance(v, int)}
            with self._lock:
                for key, value in usage.items():
                    self.usage[key] = self.usage.get(key, 0) + value
            for key, value in usage.items():
                total[key] = total.get(key, 0) + value
            emit(Event("llm", self.model, usage=usage))
            choice = response["choices"][0]
            msg = choice["message"]
            out: dict[str, Any] = {"role": "assistant", "content": msg.get("content") or ""}
            if msg.get("tool_calls"):
                out["tool_calls"] = msg["tool_calls"]
            # A reasoning model can spend the whole token budget thinking and return nothing:
            # that is not an answer, so try once more before handing back an empty reply.
            if out["content"].strip() or out.get("tool_calls") or choice.get("finish_reason") != "length":
                break
        return out, total

    def ask(self, prompt: str, *, system: str | None = None, n: int = 1, **overrides: Any) -> list[str]:
        """``n`` independent completions of a single prompt (sampled in parallel)."""
        messages = ([{"role": "system", "content": system}] if system else []) + [{"role": "user", "content": prompt}]
        if n == 1:
            return [self.chat(messages, **overrides)["content"]]
        with ThreadPoolExecutor(min(n, 8)) as pool:
            return list(pool.map(lambda _: self.chat(messages, **dict(overrides))["content"], range(n)))

    def _create(self, kwargs: dict[str, Any]) -> Any:
        """One request, adapting to what the server accepts.

        ``max_tokens`` goes first: it is the field OpenAI-compatible servers
        honor (some accept ``max_completion_tokens`` but silently ignore it,
        leaving calls uncapped). Servers that reject it - newer OpenAI models
        - get ``max_completion_tokens``. Reasoning models that reject a
        non-default ``temperature``, and clients without a per-request
        ``timeout``, are adapted to likewise. Each is learned from the first
        rejection and remembered.
        """
        kwargs = dict(kwargs)
        if self.max_tokens is not None:
            kwargs[self._tokens_param or "max_tokens"] = self.max_tokens
        if self.timeout is not None:
            kwargs["timeout"] = self.timeout
        kwargs = {k: v for k, v in kwargs.items() if k not in self._unsupported}
        try:
            response = self.client.chat.completions.create(**kwargs)
        except Exception as e:
            retry = self._adapt(kwargs, e)
            if retry is None:
                raise
            return self._create({k: v for k, v in retry.items() if k not in ("max_tokens", "max_completion_tokens", "timeout")})
        if self.max_tokens is not None and self._tokens_param is None:
            self._tokens_param = "max_tokens"
        return response

    def _adapt(self, kwargs: dict[str, Any], error: Exception) -> dict[str, Any] | None:
        """A corrected request after a rejection we know how to fix, else None."""
        text = str(error)
        if "max_tokens" in kwargs and re.search(r"max_tokens.*(unsupported|not supported)|max_completion_tokens", text, re.I):
            self._tokens_param = "max_completion_tokens"
            return kwargs
        if "timeout" in kwargs and isinstance(error, TypeError) and "timeout" in text:
            self._unsupported.add("timeout")
            return kwargs
        if "temperature" in kwargs and "temperature" in text and re.search(r"unsupported|not support|only the default", text, re.I):
            self._unsupported.add("temperature")
            return {k: v for k, v in kwargs.items() if k != "temperature"}
        return None


def _plain(obj: Any) -> Any:
    """OpenAI SDK pydantic objects -> plain dicts."""
    if hasattr(obj, "model_dump"):
        return obj.model_dump()
    if isinstance(obj, dict):
        return {k: _plain(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_plain(v) for v in obj]
    return obj
