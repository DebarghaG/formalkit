from __future__ import annotations

import json
import re

from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir


# Evaluates through ProbLog's Python API and writes the results to a file, so
# whatever the program itself prints cannot be mistaken for a query result.
DRIVER = """
import json
from problog import get_evaluatable
from problog.program import PrologFile

def save(obj):
    with open("results.json", "w") as f:
        json.dump(obj, f)

try:
    result = get_evaluatable().create_from(PrologFile("model.pl")).evaluate()
    save({"probabilities": {str(k): float(v) for k, v in result.items()}})
except BaseException as exc:
    save({"error": [type(exc).__name__, str(exc)]})
"""


class ProbLog(Adapter):
    spec = Spec(
        name="problog",
        family="LP",
        language="ProbLog (probabilistic Prolog)",
        emits="facts and rules, optionally annotated with probabilities (p::fact), evidence(...) and query(...) declarations.",
        authority="exact probabilistic inference by weighted model counting over the program's possible worlds.",
        feedback="the probability of every query (conditioned on any evidence), inconsistent evidence, parse and clause errors.",
        use="relational reasoning under uncertainty, diagnosis, Bayesian-network-style queries.",
        guidance=(
            "Write a complete program with at least one query(Atom). Probabilistic facts are 'p::fact.', "
            "annotated disjunctions 'p1::a; p2::b.', observations 'evidence(atom, true).'. "
            "sat means inference succeeded; details.model maps each query atom to its probability. "
            "unsat means the evidence is inconsistent (has probability 0). A claim is certain when its query "
            "has probability 1.0 and impossible at 0.0."
        ),
        example="0.6::rain. 0.2::sprinkler.\nwet :- rain.\nwet :- sprinkler.\nquery(wet).",
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        bad = _invalid_disjunctions(code)
        if bad:  # ProbLog only notices when every head is relevant to some query
            return Result(Verdict.ERROR, "annotated disjunction probabilities sum to more than 1: " + "; ".join(bad))
        with workdir({"model.pl": code, "driver.py": DRIVER}) as d:
            proc = sh(["python3", "driver.py"], cwd=d, timeout=timeout)
            out = d / "results.json"
            data = json.loads(out.read_text()) if out.exists() else None
        if proc.timed_out:
            return timed_out(proc, "ProbLog did not finish within the time limit (unbounded recursion or a very large grounding?)")
        printed = proc.stdout.strip()
        tail = f"\n(the program printed)\n{printed[:2000]}" if printed else ""
        if data is None:
            return Result(Verdict.ERROR, (proc.out or "problog crashed").strip())
        if "error" in data:
            kind, message = data["error"]
            if kind == "InconsistentEvidenceError":
                return Result(Verdict.UNSAT, f"{kind}: {message}{tail}", {"inconsistent_evidence": True})
            hint = ""
            if re.search(r"\bt\([^)]*\)\s*::", code):
                hint = "\nhint: t(...):: marks parameters to learn (LFI), which is not supported here - give fixed probabilities"
            return Result(Verdict.ERROR, f"{kind}: {message}{hint}{tail}")
        probabilities = data["probabilities"]
        if not probabilities:
            return Result(Verdict.ERROR, "no query results; add query(Atom)." + tail)
        text = "\n".join(f"{atom}:\t{value:.8g}" for atom, value in probabilities.items())
        return Result(Verdict.SAT, text + tail, {"model": probabilities})


_AD_HEAD = re.compile(r"(?:^|\.)\s*((?:[0-9.]+\s*::\s*[^;:.]+?;\s*)+[0-9.]+\s*::\s*[^;:.]+?)\s*(?::-|\.(?:\s|$))", re.S)
_AD_PROB = re.compile(r"([0-9]*\.?[0-9]+)\s*::")


def _invalid_disjunctions(code: str) -> list:
    """Annotated disjunctions (p1::a; p2::b ...) with numeric probabilities summing to more than 1."""
    text = re.sub(r"%[^\n]*", "", code)
    bad = []
    for m in _AD_HEAD.finditer(text):
        total = sum(float(x) for x in _AD_PROB.findall(m.group(1)))
        if total > 1 + 1e-9:
            bad.append(f"{' '.join(m.group(1).split())} (sum {total:g})")
    return bad


ADAPTER = ProbLog()
