from __future__ import annotations

import re

from formalkit.adapters._ladr import errors, has_goals, sections
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

# Mace4 exit codes (LADR manual, "Mace4 exit codes").
_EXIT = {
    0: "model found (max_models reached)",
    1: "fatal error",
    2: "search exhausted: no model within the domain-size bounds",
    3: "all models found within the domain-size bounds",
    4: "max_seconds reached with models found",
    5: "max_seconds reached without a model",
    6: "max_megs reached with models found",
    7: "max_megs reached without a model",
    101: "interrupted",
    102: "crashed",
}


_SIZE_RE = re.compile(r"^=+ DOMAIN SIZE (\d+) =+$", re.M)
_SIZES_SET_RE = re.compile(r"assign\(\s*(domain_size|end_size|start_size)\s*,", re.I)
DEFAULT_END_SIZE = 40
_GOALS_BLOCK_RE = re.compile(r"(formulas\(goals\)\.)(.*?)(end_of_list\.)", re.S)


def _conjoin_goals(code: str) -> tuple:
    """Several goals mean every one must hold (as for Prover9), but Mace4 negates each separately and
    so only finds models falsifying ALL of them; one conjunctive goal lets it refute the set."""
    m = _GOALS_BLOCK_RE.search(code)
    if not m:
        return code, False
    body = re.sub(r"%[^\n]*", "", m.group(2))
    # Each goal without its attributes (`# label(g1)`...), which cannot sit inside a conjunction.
    goals = [g.split("#", 1)[0].strip() for g in re.split(r"\.(?=\s|$)", body) if g.strip()]
    if len(goals) < 2:
        return code, False
    joined = " & ".join(f"({g})" for g in goals)
    return code[: m.start()] + f"{m.group(1)}\n  {joined}.\n{m.group(3)}" + code[m.end() :], True


def _sizes(sizes: list) -> str:
    """'4', '2..6' (contiguous) or '2, 4, 6'."""
    if len(sizes) == 1:
        return str(sizes[0])
    if sizes == list(range(sizes[0], sizes[-1] + 1)):
        return f"{sizes[0]}..{sizes[-1]}"
    return ", ".join(map(str, sizes))


class Mace4(Adapter):
    spec = Spec(
        name="mace4",
        family="finite model finder",
        language="Prover9/LADR input",
        emits="first-order assumptions and (optionally) goals in Prover9 syntax.",
        authority="finite satisfiability: existence of a finite model of the assumptions plus the negated goals.",
        feedback="finite models (interpretations of every symbol) or the size range searched.",
        use="countermodel search for conjectures, consistency checks, small-structure construction.",
        guidance=(
            "Same syntax as prover9 (names starting with u-z are variables; constants start with a-t). Mace4 searches domain sizes 2, 3, ... for a model of the assumptions "
            "together with the NEGATION of the goals (several goals are checked as one conjunction, as Prover9 "
            "reads them). With goals: refuted = a finite countermodel exists, so the "
            "goal does not follow; unknown = no countermodel of the searched sizes - NOT a proof (larger or "
            "infinite countermodels may exist; use prover9 or vampire to prove). Without goals: sat = the "
            "assumptions have a model of a searched size; unsat = the search was exhaustive over the requested "
            "sizes (details.sizes) and NO model of those sizes exists - larger sizes are not covered. Fix the "
            "sizes with assign(domain_size, N). or bound them with assign(start_size, N). / assign(end_size, N). (with goals and no size settings, sizes up to 40 are searched); "
            "without an end_size the search only stops at the time limit (unknown). Ask for several models with "
            "assign(max_models, K)."
        ),
        example=(
            "formulas(assumptions).\n  x * y = y * x.\nend_of_list.\n\n"
            "formulas(goals).\n  (x * y) * z = x * (y * z).\nend_of_list."
        ),
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        code, conjoined = _conjoin_goals(code)
        # Countermodel search with no size bound races through ever larger domains until the time
        # limit; with goals the answer is "unknown" either way unless a (small) countermodel exists.
        bounded = has_goals(code) and not _SIZES_SET_RE.search(code)
        if bounded:
            code = f"assign(end_size, {DEFAULT_END_SIZE}).\n{code}"
        result = self._search(code, timeout)
        if bounded:
            result.details["default_end_size"] = DEFAULT_END_SIZE
            result.output += f"\n(countermodel search bounded to domain sizes up to {DEFAULT_END_SIZE} by default)"
        if conjoined:
            result.details["goals_conjoined"] = True
            result.output = "(the goals were checked as one conjunction)\n" + result.output
        return result

    def _search(self, code: str, timeout: float) -> Result:
        # -c ignores Prover9-only options, so one input serves both tools. Mace4
        # does not check max_seconds between domain sizes (with no end_size it
        # grows the domain forever), so the time limit is enforced here.
        with workdir({"input.in": code}) as d:
            proc = sh(["mace4", "-c", "-t", str(max(1, int(timeout))), "-f", "input.in"], cwd=d, timeout=timeout)
        if proc.timed_out:
            sizes = sorted({int(n) for n in _SIZE_RE.findall(proc.stdout)})
            searched = f"; no model of domain size {_sizes(sizes)} was found" if sizes else ""
            result = timed_out(proc, f"time limit reached{searched} (set assign(end_size, N). to bound the search)")
            if sizes:
                result.details["sizes"] = sizes
            return result
        rc = proc.returncode
        reason = _EXIT.get(rc, f"exit code {rc}")
        models = [body for title, body in sections(proc.stdout) if title == "MODEL"]
        details = {"exit": reason}
        if rc in (1, 102) or (rc not in _EXIT):
            return Result(Verdict.ERROR, f"{reason}\n{errors(proc.out) or proc.out[-3000:]}".strip(), details)
        sizes = sorted({int(n) for n in _SIZE_RE.findall(proc.stdout)})
        if sizes:
            details["sizes"] = sizes
        if models:
            verdict = Verdict.REFUTED if has_goals(code) else Verdict.SAT
            label = "countermodel (assumptions + negated goals)" if verdict is Verdict.REFUTED else "model"
            details["counterexample" if verdict is Verdict.REFUTED else "model"] = "\n\n".join(models)
            shown = "\n\n".join(f"{label}:\n{m}" for m in models)
            return Result(verdict, f"{reason}\n{shown}", details)
        if rc == 2 and sizes:  # every requested size was searched exhaustively
            if has_goals(code):
                note = (f"no countermodel of domain size {_sizes(sizes)} exists (exhaustive); this does not prove "
                        "the goals - larger countermodels may exist")  # fmt: skip
                return Result(Verdict.UNKNOWN, f"{reason}\n{note}", details)
            note = f"no model of domain size {_sizes(sizes)} exists (exhaustive); larger sizes were not checked"
            return Result(Verdict.UNSAT, f"{reason}\n{note}", details)
        return Result(Verdict.UNKNOWN, reason, details)


ADAPTER = Mace4()
