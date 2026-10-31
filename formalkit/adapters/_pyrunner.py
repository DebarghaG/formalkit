"""Shared plumbing for backends whose input is a Python model script (cpmpy, pyomo).

The adapter writes the user's script and a backend-specific runner into a
fresh directory and runs the runner in a subprocess (so timeouts kill
cleanly). The runner execs the script, solves its top-level ``model``, and
prints one JSON payload after ``SENTINEL`` - keeping the user's own prints
separate.
"""

from __future__ import annotations

import json
import time
from typing import Sequence, Union

from formalkit.core import Result, Verdict
from formalkit.server import sh, timed_out, workdir

SENTINEL = "@@FORMALKIT@@"

# Prepended to every runner: exec the script, then `emit(payload)` ends the run.
PRELUDE = r'''
import json, os, signal, sys, time, traceback
DEADLINE = float(sys.argv[1])
try:  # cap memory below the container's limit: a hungry script gets MemoryError, not an OOM kill
    import resource
    _cap = int(int(open("/sys/fs/cgroup/memory.max").read()) * 0.75)
    resource.setrlimit(resource.RLIMIT_AS, (_cap, _cap))
except Exception:
    pass
def remaining():
    return max(1.0, DEADLINE - time.time())
def brief(exc):
    # The user's own frames (model.py) and the exception line; library internals are noise for a model.
    frames = [f for f in traceback.extract_tb(exc.__traceback__) if f.filename == "model.py"]
    shown = []
    for f in frames:  # comprehensions add a frame on the same line: show it once
        text = "  line %d: %s" % (f.lineno, (f.line or "").strip())
        if not shown or shown[-1] != text:
            shown.append(text)
    lines = ["Traceback (your script):"] + shown if shown else []
    return "\n".join(lines + traceback.format_exception_only(type(exc), exc)).strip()
def emit(payload):
    # Straight to fd 1 and out: the script may have replaced sys.stdout, or left threads running.
    for stream in (sys.stdout, sys.stderr, sys.__stdout__, sys.__stderr__):
        try:
            stream.flush()
        except Exception:
            pass
    os.write(1, ("\n@@FORMALKIT@@" + json.dumps(payload, default=str) + "\n").encode())
    try:  # children the script forked would hold stdout open: end the whole process group
        os.killpg(os.getpgid(0), signal.SIGKILL)
    finally:
        os._exit(0)
ns = {"__name__": "__main__"}
try:
    exec(compile(open("model.py").read(), "model.py", "exec"), ns)
except SystemExit:
    pass
except BaseException as e:
    emit({"error": brief(e)})
model = ns.get("model")
'''


def run_model_script(runner: str, code: str, timeout: float, args: Sequence[str] = ()) -> Union[Result, tuple]:
    """Run ``code`` under ``runner``; return an ERROR/timeout Result or ``(payload, printed)``.

    The runner sees a wall-clock deadline as ``sys.argv[1]`` (``remaining()``
    gives the solver what is left after the script built the model) and
    ``args`` after it. The process is killed shortly after the deadline.
    """
    deadline = time.time() + max(1.0, timeout - 2)
    with workdir({"model.py": code, "runner.py": PRELUDE + runner}) as d:
        proc = sh(["python3", "runner.py", repr(deadline), *args], cwd=d, timeout=timeout + 2)
    if proc.timed_out:
        return timed_out(proc)
    user_out, found, payload = proc.stdout.rpartition(SENTINEL)
    printed = _clip("\n".join(s for s in (user_out.strip(), proc.stderr.strip()) if s))
    if not found:
        why = "the script was killed (most likely it ran out of memory)" if proc.returncode in (-9, 137) \
            else "the script exited without a result"
        return Result(Verdict.ERROR, (why + "\n" + printed).strip())
    data = json.loads(payload)
    if "error" in data:
        return Result(Verdict.ERROR, data["error"].strip() + (f"\n\nprinted output:\n{printed}" if printed else ""))
    return data, printed


def _clip(text: str, limit: int = 6000) -> str:
    """Head and tail of a script's own printed output (it can print megabytes)."""
    if len(text) <= limit:
        return text
    half = limit // 2
    return f"{text[:half]}\n... <{len(text) - limit} chars of printed output omitted> ...\n{text[-half:]}"


def report(status: str, objective, values: dict, printed: str, extra: tuple = ()) -> str:
    """The text an LLM sees: status, objective, variable values, then its own prints."""
    lines = [f"status: {status}", *extra]
    if objective is not None:
        lines.append(f"objective: {objective}")
    if values:
        shown = dict(list(values.items())[:500])
        more = f" (+{len(values) - 500} more)" if len(values) > 500 else ""
        lines.append("values: " + json.dumps(shown) + more)
    if printed:
        lines.append(f"printed output:\n{printed}")
    return "\n".join(lines)
