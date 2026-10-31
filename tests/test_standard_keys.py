"""Integration tests: results carry the standard ``details`` keys (see ``formalkit.core.Result``).

Every example in ``examples/<backend>/<verdict>-<label>.<ext>`` is run, and the
result is checked against the table below:

    refuted          -> ``counterexample``
    sat / optimal    -> ``model``            (unless listed in NO_MODEL)
    proved / unsat   -> ``proof``            for backends in PROOF
    unknown          -> non-empty ``goals``  for backends in GOALS
    always           -> ``goals`` is a list of strings when present, details are JSON

lean and isabelle are covered by their own session/goal tests.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from formalkit import Verdict, backend, docker
from formalkit.registry import BACKENDS

EXAMPLES = Path(__file__).resolve().parent.parent / "examples"
SKIP = {"lean", "isabelle"}

# Backends that return a proof object behind these verdicts.
PROOF = {
    "vampire": {Verdict.PROVED, Verdict.UNSAT},
    "prover9": {Verdict.PROVED},
    "kissat": {Verdict.UNSAT},  # DRAT check summary
    "ddar": {Verdict.PROVED},
}
# Backends that list open obligations when they cannot decide.
GOALS = {"metamath", "cbmc", "esbmc", "framac", "ultimate", "spin", "ddar"}


def NO_MODEL(name: str, code: str) -> bool:
    """sat/optimal results that legitimately carry no model."""
    if name in ("z3", "cvc5"):
        return "(get-model)" not in code  # SMT solvers print a model only on request
    return False


def _cases():
    for d in sorted(p for p in EXAMPLES.iterdir() if p.is_dir() and p.name in BACKENDS and p.name not in SKIP):
        for f in sorted(d.iterdir()):
            stem = f.name.split(".")[0]
            if f.name.count(".") == 1 and stem.split("-")[0] in Verdict._value2member_map_:
                yield pytest.param(d.name, f, id=f"{d.name}/{f.name}")


@pytest.mark.docker
@pytest.mark.parametrize("name,path", list(_cases()))
def test_standard_keys(name: str, path: Path) -> None:
    if not docker.has_image(name):
        pytest.skip(f"image for {name} not built")
    stem = path.name.split(".")[0]
    code = path.read_text()
    inputs = {f.name.split(".")[1]: f.read_text() for f in path.parent.glob(f"{stem}.*.*")}
    result = backend(name).run(code, timeout=120, **inputs)
    v = result.verdict
    assert v.value == stem.split("-")[0], result.feedback()

    json.dumps(result.details)  # details must be JSON-serializable
    goals = result.details.get("goals")
    assert goals is None or (isinstance(goals, list) and all(isinstance(g, str) for g in goals)), goals

    if v is Verdict.REFUTED:
        assert result.counterexample, f"refuted without a counterexample: {result.details}"
    if v in (Verdict.SAT, Verdict.OPTIMAL) and not NO_MODEL(name, code):
        assert result.model is not None and result.model != {}, f"{v} without a model: {result.details}"
    if v in PROOF.get(name, ()):
        assert result.proof, f"{v} without a proof: {result.details}"
    if v is Verdict.UNKNOWN and name in GOALS:
        assert result.goals, f"unknown without open goals: {result.details}"
