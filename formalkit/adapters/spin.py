from __future__ import annotations

import os
import re
import time

from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

_LTL_RE = re.compile(r"^\s*ltl\b\s*(\w+)?\s*\{", re.M)
_NEVER_RE = re.compile(r"^\s*never\s*\{", re.M)
PAN_MEMORY_MB = int(os.environ.get("SPIN_MEMORY_MB", "2048"))
_ERRORS_RE = re.compile(r"errors:\s*(\d+)")
_INCOMPLETE = ("max search depth too small", "out of memory", "Search not completed", "hash table full")


def _claims(code: str) -> list[str | None]:
    """Names of the LTL properties to check, one pan run each (None = default)."""
    names: list[str | None] = []
    unnamed = 0  # spin numbers unnamed formulas among themselves: ltl_0, ltl_1, ...
    for m in _LTL_RE.finditer(code):
        if m.group(1):
            names.append(m.group(1))
        else:
            names.append(f"ltl_{unnamed}")
            unnamed += 1
    return names or ([None] if _NEVER_RE.search(code) else [])


def _strip_claims(code: str) -> str:
    """The model without its ltl blocks and never claims (for the plain safety check)."""
    out, i = [], 0
    for m in re.finditer(r"^\s*(?:ltl(?:\s+\w+)?|never)\s*\{", code, re.M):
        if m.start() < i:
            continue
        depth, j = 1, m.end()
        while j < len(code) and depth:
            depth += {"{": 1, "}": -1}.get(code[j], 0)
            j += 1
        out.append(code[i : m.start()])
        i = j
    out.append(code[i:])
    return "".join(out)


class Spin(Adapter):
    spec = Spec(
        name="spin",
        family="LTL model checker",
        language="Promela with inline LTL properties",
        emits="a Promela model of concurrent processes plus temporal formulas (ltl name { ... }) over its traces.",
        authority="trace satisfaction over the model's full state space, via automata-theoretic (Buchi) search.",
        feedback="per-property results and, on violation, the counterexample trail replayed step by step.",
        use="protocols, mutual exclusion, deadlock and liveness checking, runtime-monitor design.",
        guidance=(
            "Send one complete Promela model. Properties: inline `ltl name { [] (x >= 0) }` blocks "
            "(operators [] always, <> eventually, U until, X next, ! && || -> <->), assert() statements, "
            "or a never claim. Assertions and invalid end states (deadlocks; mark intended blocking points with "
            "`end:` labels) are always checked; every ltl block and never claim is then checked separately with "
            "acceptance-cycle search, so liveness works. "
            "proved = every property holds on every execution; refuted = some property is violated, and the "
            "output shows the counterexample trail; unknown = the search was incomplete (depth/memory bound); "
            "error = Promela syntax error. Keep models finite and small (bounded channels, byte variables)."
        ),
        example=(
            "byte x = 0;\n"
            "active proctype inc() { do :: x < 3 -> x++ :: else -> break od }\n"
            "ltl bounded { [] (x <= 3) }"
        ),
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        deadline = time.monotonic() + timeout
        with workdir({"model.pml": code}) as d:
            proc = sh(["spin", "-a", "model.pml"], cwd=d, timeout=timeout)
            if proc.timed_out:
                return timed_out(proc, "time limit reached while generating the verifier")
            if proc.returncode != 0 or not (d / "pan.c").exists():
                return Result(Verdict.ERROR, proc.out or "spin -a failed", {"stage": "spin -a"})
            claims = _claims(code)
            # Safety (assertions + invalid end states) is checked on the model
            # without its claims: under a claim, pan disables deadlock detection
            # and reports the claim's own violations. Each ltl block / never
            # claim then gets an acceptance-cycle search (-a) on the full model.
            (d / "safety").mkdir()
            (d / "safety" / "model.pml").write_text(_strip_claims(code))
            builds = [(d / "safety", ["-DSAFETY"])] + ([(d, [])] if claims else [])
            for where, flags in builds:
                if where != d:
                    proc = sh(["spin", "-a", "model.pml"], cwd=where, timeout=max(1, deadline - time.monotonic()))
                    if proc.returncode != 0 or not (where / "pan.c").exists():
                        return Result(Verdict.ERROR, proc.out or "spin -a failed", {"stage": "spin -a"})
                # MEMLIM (MB) makes pan stop with "out of memory" (-> unknown) instead of growing until the
                # container is OOM-killed; COLLAPSE compresses states so more fit.
                proc = sh(["gcc", "-O2", "-w", "-DVECTORSZ=4096", f"-DMEMLIM={PAN_MEMORY_MB}", "-DCOLLAPSE",
                           *flags, "-o", "pan", "pan.c"],
                          cwd=where, timeout=max(1, deadline - time.monotonic()))  # fmt: skip
                if proc.timed_out:
                    return timed_out(proc, "time limit reached while compiling the verifier")
                if proc.returncode != 0:
                    return Result(Verdict.ERROR, proc.out, {"stage": "compile pan.c"})

            properties: dict[str, str] = {}
            reports = []
            runs = [("safety (assertions, invalid end states)", d / "safety", ["./pan"])]
            runs += [(claim or "never claim", d, ["./pan", "-a"] + (["-N", claim] if claim else [])) for claim in claims]
            for label, where, cmd in runs:
                left = deadline - time.monotonic()
                if left < 1:
                    note = f"time limit reached before checking {label}"
                    return Result(Verdict.UNKNOWN, "\n\n".join(reports + [note, "[timeout]"]),
                                  {"properties": properties, "goals": [label], "timeout": True})  # fmt: skip
                depth = 100_000
                while True:  # deepen the search when runs are longer than the depth bound, while time remains
                    proc = sh(cmd + [f"-m{depth}"], cwd=where, timeout=max(1, deadline - time.monotonic()))
                    if (proc.timed_out or "max search depth too small" not in proc.out or depth >= 10_000_000
                            or deadline - time.monotonic() < 1):
                        break
                    depth *= 10
                if proc.timed_out:
                    properties[label] = "unknown"
                    reports.append(f"== {label}: timeout")
                    details = {"properties": properties, "goals": [label], "timeout": True}
                    return Result(Verdict.UNKNOWN, "\n\n".join(reports), details)
                m = _ERRORS_RE.search(proc.stdout)
                if m and int(m.group(1)) > 0:
                    trail = sh(["spin", "-t", "-p", "-g", "-l", "model.pml"], cwd=where,
                               timeout=max(1, deadline - time.monotonic()))  # fmt: skip
                    replay = "\n".join(l for l in trail.out.splitlines() if not l.startswith("spin: warning"))
                    properties[label] = "violated"
                    summary = "\n".join(l for l in proc.stdout.splitlines() if l.startswith("pan"))
                    if where == d:  # a claim run: pan reports an LTL violation as its never claim's assertion
                        summary = re.sub(r"assertion violated .*?\(at depth (\d+)\)",
                                         lambda m, label=label: f"ltl {label} violated (at depth {m.group(1)})", summary)  # fmt: skip
                    reports.append(f"== {label}: VIOLATED\n{summary}\ncounterexample trail:\n{replay}")
                    return Result(Verdict.REFUTED, "\n\n".join(reports), {"properties": properties, "counterexample": replay})
                if not m or any(s in proc.out for s in _INCOMPLETE):
                    properties[label] = "unknown"
                    reports.append(f"== {label}: search incomplete\n{proc.out[-2000:]}")
                    return Result(Verdict.UNKNOWN, "\n\n".join(reports), {"properties": properties, "goals": [label]})
                properties[label] = "holds"
                states = re.search(r"(\d+) states, stored", proc.stdout)
                reports.append(f"== {label}: holds (errors: 0{', ' + states.group(0) if states else ''})")
        return Result(Verdict.PROVED, "\n".join(reports), {"properties": properties})


ADAPTER = Spin()
