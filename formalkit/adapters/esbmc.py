from __future__ import annotations

import re
import time
from typing import Any, Dict, List

from formalkit.adapters._c import HEADLINE, has_option, options, qualify
from formalkit.adapters._locate import locates
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

DEFAULT_UNWIND = "50"

# Options the model may set via a `// esbmc: ...` line. Unwinding assertions
# are on by default in ESBMC 7 and cannot be turned off here, so a bounded
# PROVED is never an artifact of a too-small bound. Options that silently
# drop behaviors are absent (e.g. --context-bound, which bounds thread
# interleavings and so can hide races).
ALLOWED = {
    "--unwind": True,
    "--unwindset": True,
    "--function": True,
    "--k-induction": False,
    "--k-induction-parallel": False,
    "--incremental-bmc": False,
    "--max-k-step": True,
    "--k-step": True,
    "--interval-analysis": False,
    "--overflow-check": False,
    "--unsigned-overflow-check": False,
    "--memory-leak-check": False,
    "--nan-check": False,
    "--data-races-check": False,
    "--deadlock-check": False,
    "--no-bounds-check": False,
    "--no-pointer-check": False,
    "--no-div-by-zero-check": False,
    "--no-align-check": False,
    "--z3": False,
}

_STATE_RE = re.compile(r"^State \d+ file (\S+) line (\d+)(?: column \d+)? function (\S+)")
_ASSIGN_RE = re.compile(r"^\s+(.+?) = (.+?)(?: \([01 ]+\))?$")
_LOC_RE = re.compile(r"line (\d+)")
_DIAG_RE = re.compile(r"^(\S+?):(\d+):(\d+): (fatal error|error|warning): (.*)$")


class ESBMC(Adapter):
    spec = Spec(
        name="esbmc",
        family="Program verifier",
        language="C (with assert / __ESBMC_assume / __VERIFIER_* conventions)",
        emits="annotated C programs: assertions, assumptions, nondeterministic inputs.",
        authority="C semantics (clang front end) plus SMT-based bounded model checking, or k-induction for unbounded "
        "proofs: every assertion and built-in safety check (bounds, pointers, division by zero) holds.",
        feedback="VERIFICATION SUCCESSFUL/FAILED and, on failure, the violated property with a counterexample trace "
        "of program states.",
        use="assertion and memory-safety checking of C programs, bug finding with concrete inputs, unbounded proofs "
        "of simple loop invariants via k-induction.",
        guidance=(
            "Write a complete C program; verification starts at main(). Inputs: any undefined `nondet_*` function "
            "(e.g. `int nondet_int(void);`) or `__VERIFIER_nondet_int()` returns an arbitrary value; restrict with "
            "`__ESBMC_assume(cond);` (or `__VERIFIER_assume`). State properties with `assert(cond);` (<assert.h>). "
            "Verdicts: proved = every property holds (up to the loop bound, which is itself checked by unwinding "
            "assertions - or for all iterations with --k-induction); refuted = a property fails, with a counterexample; "
            f"unknown = the bound was too small, k-induction was inconclusive, or time ran out; error = the program "
            f"does not compile. Loops are unwound {DEFAULT_UNWIND} times by default. Signed overflow is NOT checked "
            "unless you add `--overflow-check`. Options go in a comment line, "
            "e.g. `// esbmc: --unwind 100 --overflow-check`, or `// esbmc: --k-induction --interval-analysis` for an unbounded "
            "proof (k-induction proves simple, inductive properties; for loop invariants it cannot infer, use framac or "
            "ultimate)."
        ),
        example=(
            "#include <assert.h>\nint nondet_int(void);\nint main(void) {\n  int x = nondet_int();\n"
            "  __ESBMC_assume(0 <= x && x <= 1000);\n  int y = x * x;\n  assert(y >= x);\n  return 0;\n}"
        ),
        version="ESBMC 7.11 (Z3 4.13.3)",
    )

    @locates(())
    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        args, error = options(code, "esbmc", ALLOWED)
        if error:
            return Result(Verdict.ERROR, error)
        unbounded = has_option(args, "--k-induction", "--k-induction-parallel", "--incremental-bmc")
        if not unbounded and not has_option(args, "--unwind", "--unwindset"):
            args += ["--unwind", DEFAULT_UNWIND]
        deadline = time.monotonic() + timeout
        result = self._esbmc(code, args, timeout)
        if result.verdict is Verdict.UNKNOWN and "unwinding assertion" in str(result.goals) \
                and deadline - time.monotonic() > 2:
            # ESBMC stops at the first failing property, which may be the unwinding assertion
            # while a real bug sits within the bound. Counterexamples within the bound are real.
            bounded = self._esbmc(code, [*args, "--no-unwinding-assertions"], deadline - time.monotonic())
            if bounded.verdict is Verdict.REFUTED:
                bounded.output += "\n(found within the loop bound; the bound itself is too small to prove the rest)"
                result = bounded
        return qualify(result, args)

    @staticmethod
    def _esbmc(code: str, args: List[str], timeout: float) -> Result:
        cmd = ["esbmc", "main.c", *args, "--timeout", f"{max(1, int(timeout))}s"]
        with workdir({"main.c": code}) as d:
            proc = sh(cmd, cwd=d, timeout=timeout + 10)
        if proc.timed_out:
            return timed_out(proc, "ESBMC did not finish within the time limit; reduce --unwind or simplify.")
        return interpret(proc.out)


def interpret(out: str) -> Result:
    if "VERIFICATION FAILED" in out:
        violation = _violation(out)
        trace = _trace(out)
        details: Dict[str, Any] = {"violation": violation}
        if "unwinding assertion" in violation.get("property", ""):
            details["goals"] = [f"{violation.get('property')} (line {violation.get('line')})"]
            msg = (
                f"{HEADLINE['unknown']}: loop bound insufficient ({violation.get('property')}). "
                "Raise it with `// esbmc: --unwind N`, or try `// esbmc: --k-induction`."
            )
            return Result(Verdict.UNKNOWN, msg, details)
        # Concurrent traces can carry no assignments: keep at least where the violation happened.
        details["counterexample"] = trace or [{"line": violation.get("line"), "violated": violation.get("property", "")}]
        details["core"] = [violation.get("property", "")]  # ESBMC stops at the first violated property
        lines = [HEADLINE["refuted"], f"Violated property at line {violation.get('line')}: {violation.get('property')}"]
        if violation.get("condition"):
            lines.append(f"  condition: {violation['condition']}")
        if trace:
            lines.append("Counterexample:")
            lines += [f"  line {s['line']}: {s['lhs']} = {s['value']}" for s in trace[-40:]]
        return Result(Verdict.REFUTED, "\n".join(lines), details)
    if "VERIFICATION SUCCESSFUL" in out:
        how = next((ln.strip() for ln in out.splitlines() if "Solution found by" in ln), "")
        return Result(Verdict.PROVED, " ".join([HEADLINE["proved"], how]).strip(), {"method": how})
    if "Timed out" in out:  # ESBMC's own --timeout: the tool gave up, the input is fine
        return Result(Verdict.UNKNOWN, f"{HEADLINE['unknown']}: ESBMC timed out; reduce --unwind, simplify, or "
                      "allow more time.", {"timeout": True, "goals": ["timed out"]})  # fmt: skip
    diags = [_diag(m) for m in map(_DIAG_RE.match, out.splitlines()) if m]
    errors = [d for d in diags if "error: " in d]
    if errors or "PARSING ERROR" in out or "CONVERSION ERROR" in out or "ERROR:" in out:
        other = [ln.strip() for ln in out.splitlines() if ln.startswith("ERROR")]
        if "conflicting types for '__VERIFIER_nondet" in out:
            other.append("hint: ESBMC already declares the __VERIFIER_nondet_* functions; delete your declaration "
                         "or give it the matching type (e.g. `char __VERIFIER_nondet_char(void);`).")
        return Result(Verdict.ERROR, "\n".join([HEADLINE["error"], *errors, *other]), {"diagnostics": diags})
    tail = [ln for ln in out.splitlines() if ln.strip()][-5:]
    return Result(Verdict.UNKNOWN, "\n".join([HEADLINE["unknown"], *tail]), {})


def _diag(m: "re.Match[str]") -> str:
    path, line, _col, kind, text = m.groups()
    where = f"line {line}" if path.endswith("main.c") else f"{path.rsplit('/', 1)[-1]}:{line}"
    return f"{where}: {kind}: {text}"


def _violation(out: str) -> Dict[str, Any]:
    block = out.split("Violated property:", 1)
    if len(block) < 2:
        return {}
    lines = [ln.strip() for ln in block[1].strip().splitlines()]
    loc = _LOC_RE.search(lines[0]) if lines else None
    info: Dict[str, Any] = {"line": int(loc.group(1)) if loc else None, "location": lines[0] if lines else ""}
    rest = [ln for ln in lines[1:3] if ln and not ln.startswith("VERIFICATION")]
    if rest:
        info["property"] = rest[0]
    if len(rest) > 1:
        info["condition"] = rest[1]
    return info


def _trace(out: str) -> List[Dict[str, Any]]:
    section = out.split("[Counterexample]", 1)
    if len(section) < 2:
        return []
    steps: List[Dict[str, Any]] = []
    line = None
    for raw in section[1].split("Violated property:", 1)[0].splitlines():
        m = _STATE_RE.match(raw)
        if m:
            line = int(m.group(2))
            continue
        a = _ASSIGN_RE.match(raw)
        if a and line is not None and not raw.strip().startswith("-"):
            steps.append({"line": line, "lhs": a.group(1).strip(), "value": a.group(2).strip()})
    return steps


ADAPTER = ESBMC()
