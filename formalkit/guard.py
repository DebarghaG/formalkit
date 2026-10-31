"""A formal policy in the runtime path of an agent: check every action before it runs.

    guard = formalkit.Guard(z3, POLICY, encode)      # POLICY: SMT-LIB with named rules
    decision = guard.check("transfer", {"to": "acct-7", "amount": 5000})
    decision.allowed, decision.reason                # False, "violates: within_limit"

    formalkit.Agent(llm, backends=[...], guard=guard)   # or any agent: call guard(name, args)

``encode(name, args)`` turns a proposed tool call into SMT-LIB facts about
the action, or returns None for calls the policy does not govern. The call
is allowed iff the policy plus those facts is satisfiable; when it is not,
the unsat core names the violated rules - assert them as
``(assert (! rule :named rule_name))`` with ``(set-option
:produce-unsat-cores true)``. Anything inconclusive (unknown, error, a
crashing encoder) is blocked: the guard fails closed.
"""

from __future__ import annotations

import threading
from dataclasses import dataclass, field
from typing import Any, Callable

from formalkit.client import Backend, premises
from formalkit.core import Result, Verdict


@dataclass
class Decision:
    allowed: bool
    reason: str
    result: Result | None = None


@dataclass
class Guard:
    """Allow or block proposed actions against a formal policy; counts what it saw."""

    backend: Backend
    policy: str
    encode: Callable[[str, dict], str | None]
    timeout: float = 10
    checked: int = 0
    blocked: int = 0
    log: list[tuple[str, dict, Decision]] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.kb = premises(self.backend, self.policy, name=f"{self.backend.name}_policy")
        self._lock = threading.Lock()

    def check(self, name: str, args: dict[str, Any]) -> Decision:
        try:
            facts = self.encode(name, args)
        except Exception as e:  # an action the encoder cannot describe is not provably allowed
            decision = Decision(False, f"policy encoding failed: {type(e).__name__}: {e}")
        else:
            decision = self._decide(facts)
        with self._lock:
            self.checked += 1
            self.blocked += not decision.allowed
            self.log.append((name, args, decision))
        return decision

    def _decide(self, facts: str | None) -> Decision:
        if facts is None:
            return Decision(True, "not governed by the policy")
        result = self.kb.run(f"{facts}\n(check-sat)\n(get-unsat-core)", timeout=self.timeout)
        if result.verdict is Verdict.SAT:
            return Decision(True, "complies with the policy", result)
        if result.verdict is Verdict.UNSAT:
            rules = ", ".join(result.core) if result.core else "the policy"
            return Decision(False, f"violates: {rules}", result)
        return Decision(False, f"policy check inconclusive ({result.verdict}); blocked to be safe", result)

    def __call__(self, name: str, args: dict[str, Any]) -> str | None:
        """The Agent ``guard`` protocol: None to allow, a reason to block."""
        decision = self.check(name, args)
        return None if decision.allowed else decision.reason
