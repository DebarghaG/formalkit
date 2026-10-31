from __future__ import annotations

import re
from typing import Any, Dict, List

from formalkit.adapters._c import HEADLINE, options
from formalkit.adapters._locate import locates
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

HOME = "/opt/UAutomizer-linux"

# SV-COMP property files, selected with `// ultimate: --property NAME`.
PROPERTIES = {
    "unreach-call": "CHECK( init(main()), LTL(G ! call(reach_error())) )\n",
    "no-overflow": "CHECK( init(main()), LTL(G ! overflow) )\n",
    "valid-memsafety": (
        "CHECK( init(main()), LTL(G valid-free) )\n"
        "CHECK( init(main()), LTL(G valid-deref) )\n"
        "CHECK( init(main()), LTL(G valid-memtrack) )\n"
    ),
    "termination": "CHECK( init(main()), LTL(F end) )\n",
}

ALLOWED = {"--property": True, "--architecture": True}

# Definitions supplied when the program uses but does not define them, so the
# model can write SV-COMP style code without boilerplate. They are spliced
# onto the program's first code line (no newline), so reported line numbers
# stay those of the model's own code.
_PRELUDE = {
    "reach_error": "void reach_error(void) {} ",
    "__VERIFIER_assert": "void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); } } ",
}

_RESULT_RE = re.compile(r"^Result:\s*\n(.+)$", re.M)
_PATH_RE = re.compile(r"We found a FailurePath:\s*\n(.*?)(?:\n\s*\n|\n\S*\[\d{4}-|\Z)", re.S)
_LASSO_RE = re.compile(r"(Found a nonterminating execution.*?End of lasso representation\.)", re.S)
# Entries of Ultimate's "--- Results ---" section: "  - SyntaxErrorResult [Line: 2]: Short\n    Long".
_ENTRY_RE = re.compile(r"^  - (\w+Result)(?: \[Line: (\d+)\])?: (.*)\n((?:    .*\n?)*)", re.M)
_ERROR_RESULTS = ("SyntaxErrorResult", "TypeErrorResult", "UnsupportedSyntaxResult", "ExceptionOrErrorResult")


class Ultimate(Adapter):
    spec = Spec(
        name="ultimate",
        family="Program verifier",
        language="C (SV-COMP conventions)",
        emits="C programs with __VERIFIER_assert / __VERIFIER_assume and __VERIFIER_nondet_* inputs.",
        authority="C semantics plus Ultimate Automizer's trace abstraction: unbounded proofs (it synthesizes loop "
        "invariants itself) of reachability safety, overflow freedom, memory safety or termination.",
        feedback="TRUE/FALSE/UNKNOWN for the property and, when it fails, the failure path (counterexample) with "
        "variable values, or a non-terminating lasso.",
        use="unbounded safety proofs of loops without writing invariants, termination proofs, overflow checking.",
        guidance=(
            "Write a complete C program without #include. Inputs: `extern int __VERIFIER_nondet_int(void);` (also "
            "_uint, _long, _char, _bool, ...); constrain them with `__VERIFIER_assume(cond);` or an early `return`. "
            "State properties with `__VERIFIER_assert(cond);` (plain `assert(cond)` works too) - reach_error() and "
            "__VERIFIER_assert are defined for you if missing. Floating-point programs are not supported here (use "
            "cbmc or esbmc). Verdicts: proved = the property holds on ALL executions (no loop bound); refuted = it fails, "
            "with a failure path; unknown = Ultimate gave up or timed out; error = syntax/type error or unsupported C. "
            "Default property is unreach-call (asserts never fail) on a 64-bit architecture; change with "
            "`// ultimate: --property no-overflow|valid-memsafety|termination --architecture 32bit`."
        ),
        example=(
            "extern int __VERIFIER_nondet_int(void);\nint main(void) {\n  int n = __VERIFIER_nondet_int();\n"
            "  if (n < 0 || n > 1000000) return 0;\n  int i = 0, s = 0;\n  while (i < n) { i++; s += 2; }\n"
            "  __VERIFIER_assert(s == 2 * n);\n  return 0;\n}"
        ),
        version="Ultimate Automizer 0.3.1 (native Z3 4.13.3)",
    )

    @locates(())
    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        args, error = options(code, "ultimate", ALLOWED)
        if error:
            return Result(Verdict.ERROR, error)
        opts = dict(zip(args[::2], args[1::2]))
        prop = opts.get("--property", "unreach-call")
        arch = opts.get("--architecture", "64bit")
        if prop not in PROPERTIES:
            return Result(Verdict.ERROR, f"unknown --property {prop!r}; choose one of {', '.join(PROPERTIES)}")
        if arch not in ("32bit", "64bit"):
            return Result(Verdict.ERROR, "--architecture must be 32bit or 64bit")

        if not re.search(r"\bmain\s*\([^;{]*\)\s*\{", code):
            return Result(Verdict.ERROR, f"{HEADLINE['error']}\nthe program has no main() function, so there is nothing to verify")
        if prop == "unreach-call":
            code = _checked_asserts(code)
        with workdir({"main.c": _with_prelude(code), "property.prp": PROPERTIES[prop]}) as d:
            (d / "data").mkdir()  # per-run RCP state, so concurrent runs don't share it
            cmd = [
                "python3", f"{HOME}/Ultimate.py", "--spec", "property.prp", "--architecture", arch,
                "--file", "main.c", "--full-output", "--data", str(d / "data"), "--witness-dir", str(d),
            ]  # fmt: skip
            proc = sh(cmd, cwd=d, timeout=timeout, env={"HOME": str(d)})
        if proc.timed_out:
            return timed_out(proc, "Ultimate Automizer did not finish within the time limit.")
        return interpret(proc.out, prop)


_ASSERT_H = re.compile(r"^[ \t]*#[ \t]*include[ \t]*<assert\.h>[ \t]*$", re.M)
_ASSERT_CALL = re.compile(r"(?<![\w.>])assert\s*\(")


def _checked_asserts(code: str) -> str:
    """Make plain C ``assert(c)`` count under unreach-call.

    SV-COMP's unreach-call property only tracks calls to ``reach_error``; a
    failing ``assert`` from <assert.h> is invisible to it, so a buggy program
    would be "proved". Route every ``assert`` through ``__VERIFIER_assert``
    (line numbers are kept: the include becomes an empty line).
    """
    if not _ASSERT_CALL.search(code):
        return code
    return _ASSERT_CALL.sub("__VERIFIER_assert(", _ASSERT_H.sub("", code))


def _with_prelude(code: str) -> str:
    def defined(name: str) -> bool:
        return re.search(r"\b" + name + r"\s*\([^;{]*\)\s*\{", code) is not None

    prelude = "" if defined("reach_error") else _PRELUDE["reach_error"]
    if "__VERIFIER_assert" in code and not defined("__VERIFIER_assert"):
        prelude += _PRELUDE["__VERIFIER_assert"]
    if not prelude:
        return code
    lines = code.split("\n")
    i = _first_code_line(lines)
    if i == len(lines):
        lines.append("")
    lines[i] = prelude + lines[i]
    return "\n".join(lines)


def _first_code_line(lines: List[str]) -> int:
    """Index of the first line outside leading preprocessor directives and block comments."""
    in_comment = False
    for i, line in enumerate(lines):
        s = line.strip()
        if in_comment:
            in_comment = "*/" not in s
        elif s.startswith("/*"):
            in_comment = "*/" not in s[2:]
        elif not s.startswith("#"):
            return i
    return len(lines)


def interpret(out: str, prop: str) -> Result:
    m = _RESULT_RE.search(out)
    status = m.group(1).strip() if m else "UNKNOWN"
    details: Dict[str, Any] = {"property": prop, "result": status}
    if status == "TRUE":
        return Result(Verdict.PROVED, f"{HEADLINE['proved']}: property {prop} holds on all executions", details)
    if status.startswith("FALSE"):
        trace = _counterexample(out, prop)
        details["counterexample"] = trace
        lines = [f"{HEADLINE['refuted']}: property {prop} is violated ({status})"]
        if trace:
            lines += ["Counterexample:", *[f"  {t}" for t in trace]]
        return Result(Verdict.REFUTED, "\n".join(lines), details)

    if 'Cannot run program "mathsat"' in out:
        # Bit-precise floating-point reasoning needs MathSAT, which has no arm64 build. Valid input, tool limit.
        details["goals"] = [f"property {prop}: needs MathSAT (floating point)"]
        return Result(Verdict.UNKNOWN, f"{HEADLINE['unknown']}: this program needs bit-precise floating-point "
                      "reasoning (MathSAT), which is not available in this image. Use cbmc or esbmc for programs "
                      "with floating point.", details)  # fmt: skip

    # Ultimate.py re-runs bit-precisely after a failure, so read the last run's own results.
    section = out.rsplit("--- Results ---", 1)[-1]
    entries = []
    for kind, line, short, long in _ENTRY_RE.findall(section):
        if kind in ("StatisticsResult", "GenericResult"):
            continue
        where = f"line {line}: " if line else ""
        msg = f"{where}{short.strip()}" + (f" - {' '.join(long.split())}" if long.strip() else "")
        entries.append({"kind": kind, "line": int(line) if line else None, "message": msg})
    details["results"] = entries
    errors = [e for e in entries if e["kind"] in _ERROR_RESULTS]
    if errors or status.startswith("ERROR"):
        lines = [HEADLINE["error"], *[e["message"] for e in errors]] if errors else [HEADLINE["error"], status]
        return Result(Verdict.ERROR, "\n".join(lines), details)
    reasons = [e["message"] for e in entries][:10]
    details["goals"] = reasons or [f"property {prop}: {status}"]
    return Result(Verdict.UNKNOWN, "\n".join([f"{HEADLINE['unknown']}: {status}", *reasons]), details)


def _counterexample(out: str, prop: str) -> List[str]:
    m = (_LASSO_RE if prop == "termination" else _PATH_RE).search(out)
    if not m:
        return []
    steps = []
    for ln in m.group(1).splitlines():
        if ln.strip():
            steps.append(re.sub(r"^\s*\[L(\d+)\]\s*", r"line \1: ", ln).rstrip())
    return steps[:60]


ADAPTER = Ultimate()
