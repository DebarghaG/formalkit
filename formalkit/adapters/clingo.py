from __future__ import annotations

import json
import re
import time

from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

MAX_MODELS = 10
_OPTIMIZATION = re.compile(r"#minimi[sz]e|#maximi[sz]e|:~")
_SCRIPT = re.compile(r"#script\s*\(")
_SHOW = re.compile(r"#show\b")
_NOISE = ("*** Info", "Reading from", "pyclingo version", "clingo version")


def _diagnostics(stderr: str) -> str:
    """clingo's messages with their context lines (the offending rule, notes), minus Python noise."""
    text = stderr.split("Traceback (most recent call last)")[0]
    return "\n".join(ln for ln in text.splitlines() if ln.strip() and not ln.startswith(_NOISE)).strip()


SHOWN_ATOMS = 200  # per answer set in the text; details.model always has them all


def _atoms(answer: list) -> str:
    if not answer:
        return "(empty)"
    more = len(answer) - SHOWN_ATOMS
    return " ".join(answer[:SHOWN_ATOMS]) + (f" ... ({more} more atoms, all in details.model)" if more > 0 else "")


class Clingo(Adapter):
    spec = Spec(
        name="clingo",
        family="ASP",
        language="answer set programming (clingo / ASP-Core-2)",
        emits="facts and rules with default negation, choice rules, integrity constraints, aggregates, optimization statements.",
        authority="stable models (answer sets) of the grounded program, and their optimality.",
        feedback="up to 10 answer sets (or the optimal one with its cost), unsatisfiability, grounding/parse errors.",
        use="configuration, scheduling, puzzles, defaults and exceptions, combinatorial search.",
        guidance=(
            "Write a complete logic program; use #show to restrict output to the atoms that matter "
            "(only the base program part is grounded; #program sections other than base are ignored). "
            "sat returns up to 10 answer sets in details.model (details.more says if there are others; then "
            "details.count is the total number of answer sets, exact when details.count_complete); with #show, "
            "answer sets that agree on the shown atoms count once (projection), so counts are of distinct solutions; "
            "with #minimize/#maximize/weak constraints the verdict is optimal once optimality is proven, and "
            "details.model holds the best answer set found, with details.costs (clingo reports #maximize costs negated). unsat means no answer set exists. "
            "To PROVE a claim holds in every answer set, add an integrity constraint ':- claim.' that "
            "forbids it: unsat proves the claim, an answer set is a counterexample."
        ),
        example="bird(tweety). bird(sam). penguin(sam).\nflies(X) :- bird(X), not penguin(X).\n:- flies(sam).  % does sam fly? unsat would mean yes\n#show flies/1.",
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        if _SCRIPT.search(code):
            return Result(Verdict.ERROR, "#script blocks (embedded Python/Lua) are not supported; write plain ASP.")
        deadline = time.monotonic() + timeout
        opt = bool(_OPTIMIZATION.search(code))
        args = ["--opt-mode=opt", "--models=0"] if opt else [f"--models={MAX_MODELS + 1}"]
        # With #show, solutions are what is shown: enumerate (and count) distinct projections.
        project = ["--project"] if not opt and _SHOW.search(code) else []
        args += project
        with workdir({"program.lp": code}) as d:
            proc = sh(
                ["python3", "-m", "clingo", "--outf=2", f"--time-limit={max(1, int(timeout))}", *args, "program.lp"],
                cwd=d,
                timeout=timeout + 5,
            )
            count = None
            left = deadline - time.monotonic()
            if not opt and proc.stdout.count('"Value"') > MAX_MODELS and left > 2:
                count = self._count(d, left, project)
        if proc.timed_out:
            return timed_out(proc, "clingo did not finish within the time limit")
        diagnostics = _diagnostics(proc.stderr)
        try:
            data = json.loads(proc.stdout)
        except ValueError:
            data = None
        if not data or re.search(r": error: ", diagnostics):
            return Result(Verdict.ERROR, diagnostics or proc.out)

        witnesses = [w for call in data.get("Call", []) for w in call.get("Witnesses", [])]
        answer_sets = [w.get("Value", []) for w in witnesses]
        models = data.get("Models", {})
        details = {"model": answer_sets[-MAX_MODELS:], "more": False}
        warnings = diagnostics
        status = data.get("Result")
        if status == "UNSATISFIABLE":
            return Result(Verdict.UNSAT, "\n".join(filter(None, ["UNSATISFIABLE", warnings])), {})
        if not answer_sets:
            interrupted = "INTERRUPTED" in proc.stderr or status == "UNKNOWN"
            note = "time limit reached during grounding or search" if interrupted else f"clingo result: {status}"
            return Result(Verdict.UNKNOWN, "\n".join(filter(None, [note, warnings])), {"timeout": True} if interrupted else {})

        if opt:
            details["costs"] = witnesses[-1].get("Costs", [])
            details["model"] = [answer_sets[-1]]  # the optimum (clingo reports improving answer sets)
            verdict = Verdict.OPTIMAL if models.get("Optimum") == "yes" else Verdict.SAT
            if verdict is Verdict.SAT and models.get("Optimum") == "unknown":
                details["timeout"] = True  # stopped by the time limit: the best answer set so far
            head = f"{'OPTIMUM FOUND' if verdict is Verdict.OPTIMAL else 'SATISFIABLE (optimality not proven)'}, costs {details['costs']}"
            shown = [answer_sets[-1]]
        else:
            details["more"] = len(answer_sets) > MAX_MODELS
            details["model"] = answer_sets[:MAX_MODELS]
            verdict = Verdict.SAT
            head = f"SATISFIABLE, {len(details['model'])}{'+' if details['more'] else ''} answer set(s)"
            if not details["more"] and models.get("More") not in (None, "no"):  # cut off while enumerating
                details["more"], details["timeout"] = None, True
                head += " found before the time limit (there may be more)"
            if count is not None:  # all answer sets were counted (without printing them)
                number, complete = count
                details["count"], details["count_complete"] = number, complete
                head = (f"SATISFIABLE, {number} answer sets in total (first {MAX_MODELS} shown)" if complete
                        else f"SATISFIABLE, at least {number} answer sets (counting hit the time limit; first {MAX_MODELS} shown)")
            shown = details["model"]
        lines = [head] + [f"Answer {i + 1}: {_atoms(a)}" for i, a in enumerate(shown)]
        if warnings:
            lines.append(warnings)
        return Result(verdict, "\n".join(lines), details)

    @staticmethod
    def _count(d, left: float, extra: list):
        """(number of answer sets, whether enumeration finished) - models are counted, not printed."""
        proc = sh(["python3", "-m", "clingo", "--outf=2", "--models=0", "--quiet=2", *extra,
                   f"--time-limit={max(1, int(left - 1))}", "program.lp"], cwd=d, timeout=left + 2)  # fmt: skip
        try:
            models = json.loads(proc.stdout).get("Models", {})
            return int(models["Number"]), models.get("More") == "no"
        except (ValueError, KeyError, TypeError):
            return None


ADAPTER = Clingo()
