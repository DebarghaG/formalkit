from __future__ import annotations

import json
import re
import time
from typing import Any, Dict, List

from formalkit.adapters._c import HEADLINE, has_option, options, qualify
from formalkit.adapters._locate import locates
from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

DEFAULT_UNWIND = "50"

# Options the model may set via a `// cbmc: ...` line. Unwinding assertions
# are always on (CBMC 6 default), so a PROVED verdict is never just "the
# bound was too small to reach the bug"; options that weaken that are absent
# (e.g. --depth, which silently truncates paths, or --no-unwinding-assertions).
ALLOWED = {
    "--unwind": True,
    "--unwindset": True,
    "--function": True,
    "--object-bits": True,
    "*-check": False,  # --bounds-check, --signed-overflow-check, --no-pointer-check, ...
    "--no-standard-checks": False,
    "--no-built-in-assertions": False,
    "--malloc-may-fail": False,
    "--malloc-fail-null": False,
    "--nondet-static": False,
    "--unsigned-char": False,
    "--32": False,
    "--64": False,
    "--drop-unused-functions": False,
    "--slice-formula": False,
    "--z3": False,  # SMT backend instead of bit-blasting to SAT: use for multiplication/division-heavy code
    "--smt2": False,
}


class CBMC(Adapter):
    spec = Spec(
        name="cbmc",
        family="Program verifier",
        language="C (with assert / __CPROVER_assume)",
        emits="annotated C programs: assertions, assumptions, nondeterministic inputs.",
        authority="C semantics plus bounded model checking: every assertion and built-in safety check "
        "(array bounds, pointers, division by zero, signed overflow) holds on all executions up to the loop bound.",
        feedback="the status of every property and, for each violated one, a counterexample trace of variable assignments.",
        use="checking assertions and memory safety of small C functions, finding concrete bug-triggering inputs, "
        "validating loop invariants and specifications.",
        guidance=(
            "Write a complete C program; verification starts at main() unless you set --function. Model inputs as "
            "nondeterministic values: declare `int nondet_int(void);` (any `nondet_*` function without a body returns an "
            "arbitrary value; any other function you call must be defined) and restrict them with `__CPROVER_assume(cond);`. State properties with `assert(cond);` "
            "(include <assert.h>). Verdicts: proved = every property holds for all inputs; refuted = a property fails, "
            "with a counterexample trace; unknown = the loop bound was too small (unwinding assertion failed) or time ran "
            f"out; error = the program does not compile. Loops are unwound {DEFAULT_UNWIND} times by default and an "
            "unwinding assertion checks the bound suffices, so proved is never an artifact of the bound. SV-COMP programs "
            "work too: every call to reach_error() is checked to be unreachable. Set options in a "
            "comment line, e.g. `// cbmc: --unwind 100 --unwindset main.0:10 --no-signed-overflow-check`; add `--z3` for "
            "nonlinear arithmetic (multiplication, division), which the default SAT backend handles slowly."
        ),
        example=(
            "#include <assert.h>\nint nondet_int(void);\nint main(void) {\n  int x = nondet_int();\n"
            "  __CPROVER_assume(0 <= x && x <= 1000);\n  int y = x * x;\n  assert(y >= x);\n  return 0;\n}"
        ),
        version="CBMC 6.6.0",
    )

    @locates(())
    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        args, error = options(code, "cbmc", ALLOWED)
        if error:
            return Result(Verdict.ERROR, error)
        if not has_option(args, "--unwind", "--unwindset"):
            args += ["--unwind", DEFAULT_UNWIND]
        deadline = time.monotonic() + timeout
        with workdir({"main.c": checked_reach_error(code)}) as d:
            # First the verdict: --stop-on-fail costs the same as a full run when everything holds and is
            # fast when something fails. Then, time permitting, every violated property (each with a trace:
            # with hundreds of violations that can take minutes and 100+ MB of JSON).
            proc = sh(["cbmc", "main.c", *args, "--json-ui", "--trace", "--stop-on-fail"], cwd=d, timeout=timeout)
            if proc.timed_out:
                hint = "" if has_option(args, "--z3", "--smt2") else (
                    " For multiplication/division-heavy code, try the SMT backend: `// cbmc: --z3`.")
                return timed_out(proc, "CBMC did not finish within the time limit; reduce --unwind or simplify "
                                       "the program." + hint)  # fmt: skip
            result = _parse(proc)
            if result.verdict is Verdict.REFUTED:
                full = None
                if deadline - time.monotonic() > 1:
                    full = sh(["cbmc", "main.c", *args, "--json-ui", "--trace"], cwd=d, timeout=deadline - time.monotonic())
                complete = _parse(full) if full is not None and not full.timed_out else None
                if complete is not None and complete.verdict is Verdict.REFUTED:
                    result = complete
                else:
                    result.details["first_only"] = True
                    result.output += "\n(only the first violated property is reported: listing all of them ran out of time)"
        undefined = result.details.get("undefined", [])
        library = [n for n in undefined if not _declared(code, n)]
        if library:  # declared only by a system header: CBMC simply has no model of it
            own = [n for n in undefined if n not in library]
            lines = [HEADLINE["error"], f"CBMC has no model of the library function(s) {', '.join(library)}: "
                     "implement the needed behaviour yourself (e.g. a simple loop) instead of calling them."]
            if own:
                lines.append(f"called but never defined: {', '.join(own)}. Define them, or declare them as "
                             "`nondet_*` functions without a body for an arbitrary result.")
            result.output = "\n".join(lines)
        return qualify(result, args)


_REACH_ERROR_CALL = re.compile(r"\breach_error\s*\(\s*\)\s*;")
_NOT_TYPES = {"else", "do", "return"}


def checked_reach_error(code: str) -> str:
    """Make SV-COMP's ``reach_error()`` a property CBMC checks.

    In SV-COMP programs the property is "reach_error() is never called", but
    CBMC only checks assertions: an empty ``reach_error`` body would make a
    buggy program verify. Each *call* (not a declaration or definition) gets
    a failing ``__CPROVER_assert`` in front of it, in the same statement and line.
    """

    def mark(m: "re.Match[str]") -> str:
        before = code[: m.start()].rstrip()
        word = re.search(r"([A-Za-z_]\w*)$", before)
        if word and word.group(1) not in _NOT_TYPES:  # `void reach_error();` is a declaration
            return m.group(0)
        # One statement (a comma expression), so an un-braced `if (c) reach_error();` stays intact.
        return '(__CPROVER_assert(0, "reach_error() is reachable"), reach_error());'

    return _REACH_ERROR_CALL.sub(mark, code)


def _declared(code: str, name: str) -> bool:
    """Whether the program itself declares or defines ``name`` (rather than a system header)."""
    for m in re.finditer(r"([A-Za-z_]\w*)[\s*]+" + re.escape(name) + r"\s*\(", code):
        if m.group(1) not in ("return", "else", "do", "case", "sizeof"):
            return True
    return False


def _parse(proc: Any) -> Result:
    try:
        return interpret(json.loads(proc.stdout))
    except ValueError:
        return Result(Verdict.ERROR, proc.out or f"cbmc exited with status {proc.returncode}")


def interpret(messages: List[Dict[str, Any]]) -> Result:
    errors = [m for m in messages if m.get("messageType") == "ERROR"]
    results = next((m["result"] for m in messages if "result" in m), None)
    if results is None:  # --stop-on-fail reports the violated property as a top-level object
        results = [{**m, "status": "FAILURE"} for m in messages if "property" in m and m.get("status") == "failed"]
        if not results and any(m.get("cProverStatus") == "success" for m in messages):
            results = [{"property": "all", "status": "SUCCESS", "description": "every property holds"}]
        elif not results:
            results = None
    if errors or results is None:
        lines = [_located(m.get("sourceLocation"), m.get("messageText", "")) for m in errors]
        return Result(Verdict.ERROR, "\n".join([HEADLINE["error"], *lines]) or "cbmc produced no verification result")

    props: List[Dict[str, Any]] = []
    traces: Dict[str, List[Dict[str, Any]]] = {}
    for r in results:
        loc = r.get("sourceLocation") or {}
        props.append({
            "property": r["property"],
            "status": r["status"],
            "description": r.get("description", ""),
            "line": _int(loc.get("line")),
        })  # fmt: skip
        if r["status"] == "FAILURE":
            traces[r["property"]] = _trace(r.get("trace") or [])

    if not props:  # nothing to check: a "proof" would be vacuous
        return Result(Verdict.UNKNOWN, f"{HEADLINE['unknown']}: the program has no properties to check (no assert, "
                      "no array/pointer/arithmetic operation that CBMC instruments); add assert(...) for what you "
                      "want to prove.", {"properties": [], "goals": ["no properties"]})  # fmt: skip
    failed = [p for p in props if p["status"] == "FAILURE"]
    bodiless = [p for p in failed if ".no-body." in p["property"]]
    if bodiless:  # an incomplete program, not a counterexample
        names = sorted({p["property"].rsplit(".no-body.", 1)[1] for p in bodiless})
        return Result(Verdict.ERROR, "\n".join([
            HEADLINE["error"],
            f"called but never defined: {', '.join(names)}. Define them, or (for an arbitrary result) "
            "declare them as `nondet_*` functions without a body.",
        ]), {"undefined": names})  # fmt: skip
    # Loop and recursion unwinding assertions failing means the bound was too small, not a bug.
    real = [p for p in failed if not _unwinding(p)]
    if real:
        verdict = Verdict.REFUTED
    elif failed:
        verdict = Verdict.UNKNOWN  # only unwinding assertions failed: the bound is too small
    elif all(p["status"] == "SUCCESS" for p in props):
        verdict = Verdict.PROVED
    else:
        verdict = Verdict.UNKNOWN

    lines = [f"{HEADLINE[verdict.value]} ({len(real)} of {len(props)} properties violated)"]
    if failed and not real:
        lines.append("Loop bound insufficient: raise it with `// cbmc: --unwind N` (or --unwindset LOOP:N).")
    for p in sorted(props, key=lambda p: p["status"] != "FAILURE"):
        lines.append(f"{p['status']:<8} {p['property']}  line {p['line']}: {p['description']}")
        if p["property"] in traces and p in real:
            lines.append("  counterexample:")
            lines += [f"    {_step_text(s)}" for s in traces[p["property"]][-40:]]
    details: Dict[str, Any] = {"properties": props}
    if verdict is Verdict.REFUTED:  # trace per violated property
        details["counterexample"] = {p["property"]: traces.get(p["property"], []) for p in real}
        details["core"] = [p["description"] for p in real]  # which properties fail, by their description
    elif verdict is Verdict.UNKNOWN:  # what is still open: unwinding assertions or undecided properties
        details["goals"] = [f"{p['property']} (line {p['line']}): {p['description']}" for p in props if p["status"] != "SUCCESS"]
    return Result(verdict, "\n".join(lines), details)


def _unwinding(prop: Dict[str, Any]) -> bool:
    name = prop["property"]
    return ".unwind." in name or name.endswith(".recursion") or "unwinding assertion" in prop.get("description", "")


def _trace(steps: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Keep the user-visible steps of a CBMC JSON trace."""
    out: List[Dict[str, Any]] = []
    for s in steps:
        if s.get("hidden") or s.get("internal"):
            continue
        loc = s.get("sourceLocation") or {}
        if loc.get("file", "").startswith("<"):
            continue
        kind = s.get("stepType")
        if kind == "assignment":
            value = (s.get("value") or {}).get("data")
            if value is not None:  # aggregates (arrays, structs) have no scalar value; their elements follow
                out.append({"line": _int(loc.get("line")), "lhs": s.get("lhs"), "value": value})
        elif kind == "failure":
            out.append({"line": _int(loc.get("line")), "violated": s.get("reason")})
        elif kind == "output":
            out.append({"line": _int(loc.get("line")), "output": s.get("text")})
    return out


def _step_text(s: Dict[str, Any]) -> str:
    if "violated" in s:
        return f"line {s['line']}: VIOLATED {s['violated']}"
    if "output" in s:
        return f"line {s['line']}: output {s['output']}"
    return f"line {s['line']}: {s['lhs']} = {s['value']}"


def _located(loc: Any, text: str) -> str:
    return f"line {loc['line']}: {text}" if isinstance(loc, dict) and loc.get("line") else text


def _int(x: Any) -> Any:
    try:
        return int(x)
    except (TypeError, ValueError):
        return x


ADAPTER = CBMC()
