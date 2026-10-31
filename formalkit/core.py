"""The three data types every backend speaks: Verdict, Result, Spec.

These are the formalkit equivalent of SMT-LIB's ``sat``/``unsat``/``unknown``
answers, generalized across solver families. Every backend - SMT solver,
theorem prover, planner, model checker, MILP solver - reports one
:class:`Verdict`, the raw tool output (which is what an LLM reads as
feedback), and a ``details`` dict of structured artifacts (models, unsat
cores, plans, counterexample traces, open goals, ...).

This module is stdlib-only and Python 3.9-compatible because it is also
imported inside every backend container.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from enum import Enum
from typing import Any


class Verdict(str, Enum):
    """What the backend decided, in one uniform vocabulary.

    ``PROVED``   the backend's authority certified the claim: a kernel
                 accepted the proof, an ATP found a refutation of the negated
                 conjecture, a program verifier discharged every assertion,
                 a model checker exhausted the state space.
    ``REFUTED``  the claim is false and the backend has a counterexample:
                 a countermodel, a failing execution trace, an LTL violation.
    ``SAT``      a model / solution / plan / answer set exists (see details).
    ``UNSAT``    no model / solution / plan exists.
    ``OPTIMAL``  a solution exists and is proven optimal.
    ``UNKNOWN``  the backend gave up: timeout, resource limit, incompleteness.
    ``ERROR``    the input was rejected: syntax, type, or tactic errors.

    Only the first five are *decisive*. Note that SAT-style backends only
    prove a claim under a protocol: assert its negation, and UNSAT proves it.
    """

    PROVED = "proved"
    REFUTED = "refuted"
    SAT = "sat"
    UNSAT = "unsat"
    OPTIMAL = "optimal"
    UNKNOWN = "unknown"
    ERROR = "error"

    @property
    def decisive(self) -> bool:
        return self not in (Verdict.UNKNOWN, Verdict.ERROR)

    def __str__(self) -> str:
        return self.value


@dataclass
class Result:
    """One backend run: the verdict, raw output, and structured details.

    ``details`` is backend-specific, but a few well-known keys mean the same
    thing everywhere, so pipelines can consume any backend generically:

    ``model``           the witness behind sat / optimal: an assignment,
                        solution, answer set(s), or plan.
    ``counterexample``  the witness behind refuted: a countermodel, failing
                        execution trace, violating run, or failed plan step.
    ``goals``           open obligations, as a list of strings: unsolved
                        goals, goals at ``sorry`` holes, unproved conditions.
    ``proof``           a proof object or proof text behind proved / unsat.
    ``core``            the named parts to blame, as a list of strings: an
                        unsat core of named assertions, the properties that
                        fail - localized feedback for repair and pruning.
    ``state``           a session state handle (see ``Backend.start``).
    """

    verdict: Verdict
    output: str = ""
    details: dict[str, Any] = field(default_factory=dict)
    backend: str = ""
    elapsed: float = 0.0

    @property
    def decisive(self) -> bool:
        return self.verdict.decisive

    @property
    def model(self) -> Any:
        return self.details.get("model")

    @property
    def counterexample(self) -> Any:
        return self.details.get("counterexample")

    @property
    def goals(self) -> list[str]:
        return list(self.details.get("goals") or [])

    @property
    def proof(self) -> Any:
        return self.details.get("proof")

    @property
    def core(self) -> list[str]:
        return list(self.details.get("core") or [])

    def feedback(self, limit: int = 4000) -> str:
        """Compact text for an LLM: the verdict, then head+tail of the output."""
        text = self.output.strip()
        if len(text) > limit:
            half = limit // 2
            text = f"{text[:half]}\n... <{len(text) - limit} chars truncated> ...\n{text[-half:]}"
        return f"verdict: {self.verdict.value}\n{text}".rstrip()

    def to_dict(self) -> dict[str, Any]:
        d = asdict(self)
        d["verdict"] = self.verdict.value
        return d

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> Result:
        return cls(
            verdict=Verdict(d["verdict"]),
            output=d.get("output", ""),
            details=d.get("details") or {},
            backend=d.get("backend", ""),
            elapsed=d.get("elapsed", 0.0),
        )

    def __str__(self) -> str:
        head = f"[{self.backend}] " if self.backend else ""
        return f"{head}{self.feedback()}"


@dataclass
class Spec:
    """What a backend is - the four facts an LLM needs, plus usage guidance.

    ``emits``/``authority``/``feedback``/``use`` describe the contract
    between model and tool: what the model writes, what the tool has the
    authority to decide, what comes back, and what it is good for.
    ``guidance`` and ``example`` are written for the model and end up in the
    tool description; ``inputs`` names any inputs besides ``code`` (e.g. a
    PDDL problem file next to the domain), and ``optional`` lists the ones
    that may be omitted. ``sessions`` says whether the backend supports
    step-by-step sessions (``Backend.start`` / ``State.apply``).
    ``premise_check`` is what to append to a set of premises to check them
    alone for consistency (see :func:`formalkit.premises`), e.g. ``?- true.``.
    ``timeout`` is the recommended per-run time limit in seconds (an Agent
    uses it unless told otherwise).
    """

    name: str
    family: str
    language: str
    emits: str
    authority: str
    feedback: str
    use: str
    guidance: str = ""
    example: str = ""
    inputs: dict[str, str] = field(default_factory=dict)
    optional: list[str] = field(default_factory=list)
    sessions: bool = False
    premise_check: str = ""
    timeout: float = 30
    version: str = ""

    def describe(self) -> str:
        """Tool description text for an LLM."""
        parts = [
            f"Run {self.language} through {self.name} ({self.family}).",
            f"You write: {self.emits}",
            f"It decides: {self.authority}",
            f"It returns: a verdict (proved|refuted|sat|unsat|optimal|unknown|error) "
            f"plus {self.feedback}",
        ]
        if self.guidance:
            parts.append(self.guidance.strip())
        if self.example:
            parts.append(f"Example input:\n{self.example.strip()}")
        return "\n\n".join(parts)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> Spec:
        return cls(**{k: v for k, v in d.items() if k in cls.__dataclass_fields__})
