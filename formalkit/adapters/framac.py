from __future__ import annotations

import re
from typing import List

from formalkit.adapters._c import HEADLINE, has_option, options, qualify
from formalkit.adapters._locate import locates
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

ALLOWED = {
    "-wp-fct": True,
    "-wp-prop": True,
    "-wp-timeout": True,
    "-wp-prover": True,
    "-wp-model": True,
    "-wp-split": False,
    "-wp-no-rte": False,
    "-wp-steps": True,
    "-machdep": True,
    "-main": True,
}

# "[wp] [Failed] Goal typed_twice_ensures" followed by indented "  Z3 4.8.12: Timeout ..." lines
_GOAL_RE = re.compile(r"^\[wp\] \[(\w+)\] Goal (\w+)[^\n]*\n((?:  \S[^\n]*\n)*)", re.M)
_SUMMARY_RE = re.compile(r"Proved goals:\s*(\d+)\s*/\s*(\d+)")
# "[    -    ] Post-condition (file main.c, line 3)" from -report
_REPORT_RE = re.compile(r"^\[\s*(.+?)\s*\]\s+(.*\(file \S+, line \d+\).*)$")


class FramaC(Adapter):
    spec = Spec(
        name="framac",
        family="Program verifier",
        language="C annotated with ACSL contracts",
        emits="annotated programs: ACSL function contracts (requires/ensures/assigns), loop invariants, "
        "loop variants and assertions.",
        authority="C semantics plus deductive verification (Frama-C WP): each annotation becomes a proof obligation "
        "discharged by SMT solvers, for all inputs and all loop iterations (not bounded).",
        feedback="how many proof obligations were proved and, for each unproved one, its kind, ACSL property and line.",
        use="loop invariants, function specifications, proving absence of runtime errors, proof repair.",
        guidance=(
            "Write ACSL in /*@ ... */ comments: `requires` / `ensures` / `assigns` before functions (\\result names the "
            "return value, \\old(e) the pre-state), `loop invariant` / `loop assigns` / `loop variant` before loops, "
            "`assert` inside bodies. Runtime-error checks (overflow, division by zero, out-of-bounds) are added "
            "automatically, so add `requires` bounds that rule them out. Verdicts: proved = every obligation discharged; "
            "unknown = some obligations unproved (the annotations may be wrong OR too weak: strengthen loop invariants, "
            "add requires/assigns - an unproved goal is not a counterexample); error = parse/type error in C or ACSL. Name annotations (`loop invariant inv1: ...`) to see exactly which ones fail (details.core). "
            "Options go in a comment line, e.g. `// framac: -wp-fct f -wp-timeout 20`."
        ),
        example=(
            "/*@ requires 0 <= n <= 1000;\n    ensures \\result == n * (n + 1) / 2; */\nint sum(int n) {\n  int s = 0;\n"
            "  /*@ loop invariant 0 <= i <= n + 1 && s == (i - 1) * i / 2;\n      loop assigns i, s;\n"
            "      loop variant n - i; */\n  for (int i = 1; i <= n; i++) s += i;\n  return s;\n}"
        ),
        version="Frama-C 25.0 (Manganese) WP, Why3 1.5.1, Z3 4.8.12, CVC4 1.8",
    )

    @locates(("FRAMAC_SHARE",))
    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        args, error = options(code, "framac", ALLOWED)
        if error:
            return Result(Verdict.ERROR, error)
        rte = [] if has_option(args, "-wp-no-rte") else ["-wp-rte"]
        requested = list(args)
        args = [a for a in args if a != "-wp-no-rte"]
        if not has_option(args, "-wp-prover"):
            args += ["-wp-prover", "z3,cvc4"]
        if not has_option(args, "-wp-timeout"):
            args += ["-wp-timeout", str(max(2, min(10, int(timeout / 4))))]
        cmd = ["frama-c", "main.c", "-wp", *rte, *args, "-wp-cache", "none", "-then", "-report", "-report-no-proven"]
        with workdir({"main.c": code}) as d:
            proc = sh(cmd, cwd=d, timeout=timeout)
        if proc.timed_out:
            return timed_out(proc, "Frama-C did not finish within the time limit; split the goals (-wp-fct) or simplify.")
        result = interpret(proc.out, proc.returncode)
        scope = [f"{a} {args[i + 1]}" for i, a in enumerate(args) if a in ("-wp-fct", "-wp-prop")]
        if scope and result.verdict is not Verdict.ERROR:
            # A restricted run proves only what was selected; say so wherever the verdict is read.
            result.details["scope"] = scope
            result.output += f"\nScope: only the selected goals were checked ({', '.join(scope)}); others were not."
        return qualify(result, requested)


def interpret(out: str, returncode: int) -> Result:
    if returncode != 0 or "User Error" in out or "aborted" in out:
        errors = [ln for ln in out.splitlines() if "rror" in ln or "aborted" in ln or ln.startswith("  ")]
        return Result(Verdict.ERROR, "\n".join([HEADLINE["error"], *errors[:40]]) or out)

    summary = _SUMMARY_RE.search(out)
    proved, total = (int(summary.group(1)), int(summary.group(2))) if summary else (0, 0)
    unproved = []
    for status, goal, provers in _GOAL_RE.findall(out):
        if status not in ("Qed", "Valid", "Proved"):
            tried = ", ".join(" ".join(ln.split()) for ln in provers.splitlines() if ln.strip())
            unproved.append({"goal": goal, "status": status, "provers": tried})
    report = _report(out)
    goals = [f"[{u['status']}] {u['goal']}" + (f" ({u['provers']})" if u["provers"] else "") for u in unproved]
    details = {"proved": proved, "total": total, "goals": goals, "unproved_properties": report}
    if report:
        # Blame by ACSL name (e.g. `loop invariant c1: ...`), so callers like Houdini can drop exactly
        # the failing annotations; unnamed properties are blamed by their description.
        details["core"] = [_label(r) for r in report]

    if total == 0:
        return Result(
            Verdict.UNKNOWN,
            "No proof obligations were generated: add ACSL annotations (requires/ensures/loop invariant/assert).",
            details,
        )
    verdict = Verdict.PROVED if proved == total else Verdict.UNKNOWN
    lines = [f"{HEADLINE[verdict.value]}: {proved} / {total} proof obligations proved"]
    if unproved and any(k in u["goal"] for u in unproved for k in ("free", "malloc", "calloc", "realloc")):
        # WP's typed memory model rarely discharges dynamic-allocation obligations, even for correct code.
        lines.append("hint: WP handles malloc/free poorly; check allocation-heavy code with cbmc or esbmc instead.")
    if unproved:
        lines.append("Unproved goals:")
        lines += [f"  {g}" for g in goals]
    if report:
        lines.append("Unproved ACSL properties:")
        lines += [f"  {r}" for r in report]
    return Result(verdict, "\n".join(lines), details)


def _label(prop: str) -> str:
    m = re.search(r"'([^']+)'", prop)
    return m.group(1) if m and not m.group(1).startswith("rte,") else prop


def _report(out: str) -> List[str]:
    """ACSL properties the -report section lists as not proved, with their lines."""
    section = out.split("[report] Computing properties status...", 1)
    if len(section) < 2:
        return []
    keep = []
    for line in section[1].splitlines():
        m = _REPORT_RE.match(line.strip())
        if m and m.group(1).lower() != "valid":
            keep.append(m.group(2).replace("(file main.c, ", "("))
    return keep


ADAPTER = FramaC()
