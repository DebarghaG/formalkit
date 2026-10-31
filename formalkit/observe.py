"""Events: every backend run, session step and LLM call, as data.

    with formalkit.observe(trace := formalkit.Trace()):
        step_search(root, llm_steps(llm))
    trace.tactics()        # (goals, tactic, outcome) triples - successes and failures

    with formalkit.observe(formalkit.Budget(calls=200, tokens=1_000_000)):
        ...                # stops with BudgetExceeded when either runs out

Observers are plain callables taking an :class:`Event`. They see every
tool execution, including those inside patterns, portfolios, compiled
backends and worker threads, so one mechanism yields training data
(proofs, tactic triples, failed paths), cost control and logging.
Observers are process-wide while their ``with`` block is active.
"""

from __future__ import annotations

import threading
import time
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Any, Callable, Iterator

from formalkit.core import Result, Verdict

_observers: list[Callable[[Event], None]] = []
_lock = threading.Lock()


@dataclass
class Event:
    """One thing that happened.

    ``kind`` is ``"run"`` (a whole input checked), ``"start"`` / ``"step"``
    (a session opened / a step applied to ``parent``, a state id) or
    ``"llm"`` (a model call; ``usage`` holds its tokens).
    """

    kind: str
    backend: str = ""
    input: str = ""
    result: Result | None = None
    parent: str | None = None
    usage: dict[str, int] = field(default_factory=dict)
    time: float = field(default_factory=time.time)


@contextmanager
def observe(observer: Callable[[Event], None]) -> Iterator[Callable[[Event], None]]:
    """Send every event to ``observer`` while the block runs."""
    with _lock:
        _observers.append(observer)
    try:
        yield observer
    finally:
        with _lock:
            _observers.remove(observer)


def emit(event: Event) -> None:
    """Deliver ``event`` to the active observers (an observer may raise, e.g. a Budget)."""
    with _lock:
        observers = list(_observers)
    for observer in observers:
        observer(event)


class BudgetExceeded(RuntimeError):
    """Raised by a :class:`Budget` from inside the run that exhausted it."""


class Budget:
    """Limit backend calls, LLM tokens and wall-clock seconds for a block of work.

    ``None`` means unlimited. Check ``budget.spent`` afterwards to see the cost.
    """

    def __init__(self, calls: int | None = None, tokens: int | None = None, seconds: float | None = None) -> None:
        self.calls, self.tokens, self.seconds = calls, tokens, seconds
        self.spent = {"calls": 0, "tokens": 0}
        self.started = time.monotonic()
        self._lock = threading.Lock()

    def __call__(self, event: Event) -> None:
        with self._lock:
            if event.kind == "llm":
                self.spent["tokens"] += event.usage.get("total_tokens", 0)
            else:
                self.spent["calls"] += 1
            over = [
                name
                for name, limit, used in (
                    ("calls", self.calls, self.spent["calls"]),
                    ("tokens", self.tokens, self.spent["tokens"]),
                    ("seconds", self.seconds, time.monotonic() - self.started),
                )
                if limit is not None and used > limit
            ]
        if over:
            raise BudgetExceeded(f"budget exceeded: {', '.join(over)} (spent {self.spent})")


class Trace:
    """An observer that records events and turns them into training data.

    The views are what the learning-from-feedback literature trains on:
    verified proofs (expert iteration, synthetic data), (state, step,
    outcome) triples including failures (step-level supervision, failed
    search paths), and preference pairs between a step that worked and
    one that failed from the same state (DPO on compiler feedback).
    """

    def __init__(self) -> None:
        self.events: list[Event] = []
        self._goals: dict[str, list[str]] = {}  # state id -> its goals
        self._lock = threading.Lock()

    def __call__(self, event: Event) -> None:
        with self._lock:
            self.events.append(event)
            if event.result is not None and event.result.details.get("state"):
                self._goals[event.result.details["state"]] = event.result.goals

    def __len__(self) -> int:
        return len(self.events)

    def proofs(self) -> list[dict[str, Any]]:
        """Every input a backend proved: ``{"backend", "input", "proof"}``."""
        out = []
        for e in self.events:
            if e.result is not None and e.result.verdict is Verdict.PROVED:
                proof = e.result.proof if e.kind == "step" else e.input
                out.append({"backend": e.backend, "input": e.input, "proof": proof if isinstance(proof, str) else e.input})
        return out

    def tactics(self) -> list[dict[str, Any]]:
        """Every session step: ``{"goals", "tactic", "outcome"}`` with outcome
        ``"solved"``, ``"progress"`` or ``"error"`` (with the error text)."""
        out = []
        for e in self.events:
            if e.kind != "step" or e.result is None:
                continue
            r = e.result
            outcome = "solved" if r.verdict is Verdict.PROVED else "error" if r.verdict is Verdict.ERROR else "progress"
            row = {"goals": self._goals.get(e.parent or "", []), "tactic": e.input, "outcome": outcome}
            if outcome == "error":
                row["error"] = r.output
            else:
                row["next_goals"] = r.goals
            out.append(row)
        return out

    def preferences(self) -> list[dict[str, Any]]:
        """Pairs of steps from the same state where one worked and one failed:
        ``{"goals", "chosen", "rejected"}``."""
        by_parent: dict[str, list[dict[str, Any]]] = {}
        for e in self.events:
            if e.kind == "step" and e.result is not None and e.parent:
                by_parent.setdefault(e.parent, []).append({"tactic": e.input, "ok": e.result.verdict is not Verdict.ERROR,
                                                            "solved": e.result.verdict is Verdict.PROVED})  # fmt: skip
        pairs = []
        for parent, steps in by_parent.items():
            good = sorted((s for s in steps if s["ok"]), key=lambda s: not s["solved"])
            bad = [s for s in steps if not s["ok"]]
            for g in good[:1]:
                pairs += [{"goals": self._goals.get(parent, []), "chosen": g["tactic"], "rejected": b["tactic"]} for b in bad]
        return pairs
