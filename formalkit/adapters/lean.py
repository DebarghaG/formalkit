from __future__ import annotations

import itertools
import json
import os
import queue
import re
import shutil
import signal
import subprocess
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from collections import OrderedDict
from typing import Optional

from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

PROJECT = os.environ.get("LEAN_PROJECT", "/opt/lean-project")
REPL = os.environ.get("LEAN_REPL", "/opt/repl/.lake/build/bin/repl")
# Declaring axioms is an escape hatch: anything follows from `axiom h : False`.
_AXIOM_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*axiom\s+(\S+)", re.M)
_SORRY_RE = re.compile(r"declaration uses ['`]sorry['`]")
_HOLE_RE = re.compile(r"(?<![\w.'])sorry(?![\w'])")
MAX_REPLS = 2  # distinct import headers kept warm (Mathlib alone takes GBs)
# Each check runs up to three Lean processes (compile, then replay + audit). Bound how many
# checks run at once so a burst (e.g. sketch_and_fill trying a dozen candidates for several
# problems) queues instead of thrashing the CPU until everything times out.
_JOBS = threading.BoundedSemaphore(int(os.environ.get("FORMALKIT_LEAN_JOBS", max(2, (os.cpu_count() or 4) // 2))))
MODULE = "FormalkitCheck"  # the module name a checked file is compiled as
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
_CLAIM_RE = re.compile(r"(?<![\w.'])(theorem|lemma|example)(?![\w'])")
_NATIVE_RE = re.compile(r"native_decide|\+\s*native\b|ofReduceBool|ofReduceNat")
_AUDIT = f"""import {MODULE}
import Lean
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let some idx := env.getModuleIdx? `{MODULE} | throwError "module not found"
  for n in env.header.moduleData[idx.toNat]!.constNames do
    let axs ← Lean.collectAxioms n
    IO.println s!"AXIOMS {{n}} {{axs.toList}}"
  IO.println "AUDIT-DONE NONCE"
"""
# Commands that run arbitrary code while the file is checked. Their output is still
# reported, but a file using them is never certified: the code could tamper with the
# checking itself.
_EXEC_RE = re.compile(
    r"(#eval!?|#exec|\brun_cmd|\brun_elab|\brun_meta|\brun_tac|\bby_elab|\binitialize|\bbuiltin_initialize"
    r"|\belab_rules|\belab)(?![\w'!])"
    r"|@\[[^\]]*\b(command_elab|term_elab|tactic|init|implemented_by|extern)\b",
)
MAX_STATES = 50_000


def _audit(d, env: dict, deadline: float) -> Optional[tuple]:
    """Independent checks of a file that elaborated cleanly; None when it passes.

    1. Kernel replay (``leanchecker``): re-checks every declaration of the
       compiled module, catching anything added while the kernel was
       bypassed (e.g. ``set_option debug.skipKernelTC``).
    2. Axiom audit: every declaration may use only propext,
       Classical.choice and Quot.sound - no sorryAx, no native_decide
       auxiliary axioms, no user axioms.
    """
    nonce = uuid.uuid4().hex
    (d / "Audit.lean").write_text(_AUDIT.replace("NONCE", nonce))
    # The audit certifies an already-elaborated file: give it a floor even when the compile
    # used most of the budget (the client allows 60s of slack beyond the timeout).
    left = max(30.0, deadline - time.monotonic())
    with ThreadPoolExecutor(2) as pool:
        replay = pool.submit(sh, ["leanchecker", MODULE], cwd=d, timeout=left, env=env)
        audit = pool.submit(sh, ["lean", "Audit.lean"], cwd=d, timeout=left, env=env)
        replay, audit = replay.result(), audit.result()
    if replay.timed_out or audit.timed_out:
        return Verdict.UNKNOWN, "the independent kernel replay / axiom audit did not finish in time; not certified."
    if replay.returncode != 0:
        return Verdict.ERROR, "the kernel replay rejected the file (a declaration bypassed the kernel):\n" + replay.out
    if audit.returncode != 0 or f"AUDIT-DONE {nonce}" not in audit.stdout.splitlines():
        return Verdict.UNKNOWN, "the axiom audit did not complete:\n" + audit.out
    bad = []
    for line in audit.stdout.splitlines():
        m = re.match(r"AXIOMS (\S+) \[(.*)\]$", line.strip())
        if m:
            extra = [a.strip() for a in m.group(2).split(",") if a.strip() and a.strip() not in STANDARD_AXIOMS]
            if extra:
                bad.append(f"{m.group(1)} depends on {', '.join(extra)}")
    if bad:
        return Verdict.ERROR, "non-standard axioms are not accepted as proof:\n" + "\n".join(bad)
    return None


def _lean_path() -> str:
    try:
        with open(os.path.join(PROJECT, "LEAN_PATH")) as f:
            return f.read().strip()
    except OSError:
        return ""


def _fmt(messages: list, line_offset: int = 0) -> str:
    return "\n\n".join(
        f"{(m['line'] or 0) + line_offset}:{m['column']}: {m['severity']}: {m['message']}" for m in messages
    )


def _message(m: dict) -> dict:
    pos = m.get("pos") or {}
    return {
        "severity": m.get("severity", "information"),
        "line": pos.get("line"),
        "column": pos.get("column"),
        "message": (m.get("data") or "").strip(),
    }


def _unsolved_goals(messages: list) -> list:
    """Goals listed by `unsolved goals` errors, one string per goal."""
    goals = []
    for m in messages:
        if m["severity"] == "error" and m["message"].startswith("unsolved goals"):
            body = m["message"].split("\n", 1)[1] if "\n" in m["message"] else ""
            goals += [g.strip() for g in body.split("\n\n") if g.strip()]
    return goals


_CHAR_LIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")


def _IDENT_CHAR(c: str) -> bool:  # noqa: N802
    return c.isalnum() or c in "_'!?.₀₁₂₃₄₅₆₇₈₉"


def _mask(code: str) -> str:
    """``code`` with comments and string literals blanked out (same length, newlines kept)."""
    out, i, n = list(code), 0, len(code)

    def blank(a: int, b: int) -> None:
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        if code.startswith("--", i):
            j = code.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif code.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if code.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif code.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            blank(i, j)
            i = j
        elif code[i] == '"':
            j = i + 1
            while j < n and code[j] != '"':
                j += 2 if code[j] == "\\" else 1
            blank(i, min(j + 1, n))
            i = j + 1
        elif code[i] == "'" and (i == 0 or not _IDENT_CHAR(code[i - 1])) and _CHAR_LIT.match(code, i):
            j = _CHAR_LIT.match(code, i).end()  # a char literal such as '"' is not a string opener
            blank(i, j)
            i = j
        else:
            i += 1
    return "".join(out)


def _split_header(code: str) -> tuple:
    """(import header, body, number of header lines). Imports must come first in Lean."""
    masked = _mask(code)
    lines = masked.split("\n")
    count = 0
    for k, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("import "):
            count = k + 1
        elif stripped:
            break
    cut = len("\n".join(code.split("\n")[:count])) + (1 if count else 0)
    return code[:cut], code[cut:], count


# -- the REPL -----------------------------------------------------------------------

_generations = itertools.count(1)


class _Repl:
    """One long-lived `repl` process with its import header loaded once.

    Callers hold ``lock`` around ``command``. A crash or timeout kills the
    process; states minted under the old ``generation`` then expire.
    """

    def __init__(self, header: str) -> None:
        self.header = header
        self.lock = threading.Lock()
        self.proc: Optional[subprocess.Popen] = None
        self.lines: "queue.Queue[Optional[str]]" = queue.Queue()
        self.env: Optional[int] = None
        self.generation = 0

    @property
    def alive(self) -> bool:
        return self.proc is not None and self.proc.poll() is None

    def kill(self) -> None:
        if self.proc is not None:
            try:
                os.killpg(self.proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            self.proc.wait()
        self.proc, self.env = None, None

    def ensure(self, timeout: float) -> Optional[list]:
        """Start the process and load the header; returns header errors, if any."""
        if self.alive:
            return None
        self.kill()
        self.proc = subprocess.Popen(
            [REPL],
            cwd=PROJECT,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            encoding="utf-8",
            env={**os.environ, "LEAN_PATH": _lean_path()},
            start_new_session=True,
        )
        self.lines = queue.Queue()
        stdout, lines = self.proc.stdout, self.lines

        def pump() -> None:
            for line in stdout:
                lines.put(line)
            lines.put(None)

        threading.Thread(target=pump, daemon=True).start()
        self.generation = next(_generations)
        if self.header.strip():
            resp = self._send({"cmd": self.header}, timeout)
            errors = [_message(m) for m in resp.get("messages", []) if m.get("severity") == "error"]
            if errors or "env" not in resp:
                self.kill()
                return errors or [{"severity": "error", "line": 1, "column": 0, "message": str(resp)}]
            self.env = resp["env"]
        return None

    def command(self, request: dict, timeout: float) -> dict:
        if "cmd" in request and self.env is not None:
            request = {**request, "env": self.env}
        return self._send(request, timeout)

    def _send(self, request: dict, timeout: float) -> dict:
        assert self.proc is not None and self.proc.stdin is not None
        try:
            self.proc.stdin.write(json.dumps(request) + "\n\n")
            self.proc.stdin.flush()
        except OSError:
            self.kill()
            raise RuntimeError("the Lean REPL stopped unexpectedly (a crash or out of memory)") from None
        buf: list = []
        while True:
            try:
                line = self.lines.get(timeout=timeout)
            except queue.Empty:
                self.kill()
                raise TimeoutError from None
            if line is None:
                self.kill()
                raise RuntimeError("the Lean REPL stopped unexpectedly (a crash or out of memory)")
            if line.strip():
                buf.append(line)
            elif buf:
                return json.loads("".join(buf))


class _Pool:
    """At most MAX_REPLS warm REPLs, one per import header, least recently used evicted."""

    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.repls: "OrderedDict[str, _Repl]" = OrderedDict()

    def get(self, header: str) -> _Repl:
        key = header.strip()
        with self.lock:
            if key in self.repls:
                self.repls.move_to_end(key)
                return self.repls[key]
            while len(self.repls) >= MAX_REPLS:
                _, victim = self.repls.popitem(last=False)
                with victim.lock:  # let its in-flight command finish
                    victim.kill()
            repl = self.repls[key] = _Repl(header)
            return repl


class _Hole:
    """A session's origin: the code, the hole's span, and where it lives."""

    def __init__(self, code: str, start: int, end: int) -> None:
        self.code, self.start, self.end = code, start, end


class _State:
    def __init__(self, repl: _Repl, generation: int, proof_state: int, hole: _Hole, path: tuple) -> None:
        self.repl, self.generation, self.proof_state, self.hole, self.path = repl, generation, proof_state, hole, path


# -- assembling a finished session into a checkable file ------------------------------


def _indent(tactics: tuple, column: int) -> str:
    """Tactics stacked at ``column``; the first one starts at the current position."""
    pad = "\n" + " " * column
    return pad.join(t.replace("\n", pad) for t in tactics)


def _assemblies(hole: _Hole, tactics: tuple) -> list:
    """Candidate files with the hole replaced by the tactic path, most likely first.

    Lean's tactic blocks are indentation-sensitive and a hole can sit in
    tactic or term position, so there are a few shapes; the kernel check
    decides which one is right.
    """
    code, start, end = hole.code, hole.start, hole.end
    line_start = code.rfind("\n", 0, start) + 1
    column = start - line_start
    before = _mask(code)[line_start:start]
    rest_of_line = code[end:].split("\n", 1)[0]
    head, tail = code[:start], code[end:]
    own_line = before.strip() == ""
    after_by = re.search(r"(?<![\w.])by\s*$", before) is not None and not _mask(rest_of_line).strip()
    term_like = re.search(r"(:=|\(|,|\bfrom|\bexact)\s*$", _mask(code)[:start]) is not None

    own = head + _indent(tactics, column) + tail
    paren = head + "(" + _indent(tactics, column + 1) + "\n" + " " * column + ")" + tail
    term = head + "(by\n" + " " * (column + 2) + _indent(tactics, column + 2) + "\n" + " " * column + ")" + tail
    if after_by:
        indent = len(code[line_start:start]) - len(code[line_start:start].lstrip()) + 2
        return [head.rstrip() + "\n" + " " * indent + _indent(tactics, indent) + tail, paren]
    if own_line:
        return [term, own] if term_like else [own, term]
    return [term, paren] if term_like else [paren, term]


class Lean(Adapter):
    spec = Spec(
        version="Lean 4.35.0, Mathlib v4.35.0",
        name="lean",
        timeout=120,
        family="Interactive theorem prover",
        language="Lean 4 (with Mathlib)",
        emits="theorem statements, tactic scripts, proof terms.",
        authority="kernel-checked dependent type theory.",
        feedback=(
            "the elaborator's messages with line/column: errors, unsolved goals with their local contexts, "
            "failed tactics, #eval/#check output; open goals (also those at each `sorry`) in details['goals']."
        ),
        use="library-scale mathematics, certified programs.",
        guidance=(
            "Send one complete Lean 4 file. Start with `import Mathlib` if you need Mathlib (loading it takes "
            "a few seconds; use timeouts of 60s or more). Verdicts: proved = the file elaborated with no errors "
            "and no `sorry`; error = Lean rejected something (the messages show unsolved goals and their hypotheses "
            "- use them to repair the proof); unknown = the file checks but still contains `sorry` (incomplete; "
            "the goal at each `sorry` is reported). What counts as a proof: the kernel re-checks every declaration "
            "and only the standard axioms may be used, so `axiom` declarations, `native_decide`/`decide +native` "
            "and `#exit` give error, and a file that runs code while it is checked (`#eval`, `run_cmd`, `run_tac`, "
            "`elab`...) or states no theorem/lemma/example is reported unknown - use `#eval` only to explore. A useful "
            "pattern is to state the theorem, try a tactic (`simp`, `omega`, `norm_num`, `linarith`, `aesop`, "
            "`decide`, `exact?`), and read the remaining goal."
        ),
        example="import Mathlib\n\ntheorem two_mul_gt (x : ℕ) (h : 5 < x) : 10 < 2 * x := by\n  omega",
        sessions=True,
        inputs={
            "challenge": "Optional: the fixed statement file (theorems with `sorry`) this file must prove. A proof is "
                         "then certified at the end by `lake comparator`: same statements, standard axioms, kernel-checked.",
            "paranoid": "Optional: 'true' to also run every external checker bundled with Lean.",
        },
        optional=["challenge", "paranoid"],
    )

    def __init__(self) -> None:
        self.pool = _Pool()
        self.states: "OrderedDict[str, _State]" = OrderedDict()
        self.states_lock = threading.Lock()

    # -- whole files ------------------------------------------------------------------

    def run(self, code: str, timeout: float, challenge: str = "", paranoid: str = "", **inputs: str) -> Result:
        deadline = time.monotonic() + timeout
        if not _JOBS.acquire(timeout=timeout):
            return Result(Verdict.UNKNOWN, "Lean is busy with other checks; not checked in time.", {"timeout": True})
        try:
            result = self._run(code, max(1.0, deadline - time.monotonic()), deadline)
            if result.verdict is Verdict.PROVED and challenge.strip():  # certification: at the end, against a statement
                result = _certify(code, result, challenge, paranoid.strip().lower() == "true", max(120.0, timeout))
            return result
        finally:
            _JOBS.release()

    def _run(self, code: str, timeout: float, deadline: float) -> Result:
        masked = _mask(code)
        axioms = _AXIOM_RE.findall(masked)
        with workdir({f"{MODULE}.lean": code}) as d:
            env = {"LEAN_PATH": f"{_lean_path()}:{d}"}
            proc = sh(["lean", "--json", f"{MODULE}.lean", "-o", f"{MODULE}.olean"], cwd=d, timeout=timeout, env=env)
            if proc.timed_out:
                return timed_out(proc)
            messages, other = [], []
            for line in proc.stdout.splitlines():
                try:
                    messages.append(_message(json.loads(line)))
                except ValueError:
                    if line.strip():
                        other.append(line)
            output = _fmt(messages)
            extra = "\n".join(other + ([proc.stderr.strip()] if proc.stderr.strip() else []))
            if extra:
                output = (output + "\n" + extra).strip()
            errors = [m for m in messages if m["severity"] == "error"]
            sorries = [m for m in messages if _SORRY_RE.search(m["message"])]
            details = {"messages": messages, "sorries": len(sorries), "axioms": axioms, "goals": _unsolved_goals(messages)}
            if errors or proc.returncode != 0 and not messages:
                return Result(Verdict.ERROR, output or f"lean exited with code {proc.returncode}", details)
            if axioms:
                note = f"axiom declarations are not allowed (they can prove anything): {', '.join(axioms)}"
                return Result(Verdict.ERROR, (output + "\n" + note).strip(), details)
            if any(m["message"].startswith("using 'exit' to interrupt Lean") for m in messages):
                note = "`#exit` is not allowed: everything after it would go unchecked."
                return Result(Verdict.ERROR, (output + "\n" + note).strip(), details)
            if sorries:
                goals = self._sorry_goals(code, timeout)
                details["goals"] = goals
                if goals:
                    listing = "\n\n".join(f"goal at sorry #{i}:\n{g}" for i, g in enumerate(goals, 1))
                    output = f"{output}\n\n{listing}".strip()
                return Result(Verdict.UNKNOWN, output, details)
            if not _CLAIM_RE.search(masked):
                note = "nothing was proved: the file states no theorem, lemma or example."
                return Result(Verdict.UNKNOWN, (output + "\n" + note).strip(), details)
            execs = sorted({m.group(1) or m.group(2) for m in _EXEC_RE.finditer(masked)})
            if execs:
                note = (f"not certified: the file runs code while it is checked ({', '.join(execs)}), which could "
                        "interfere with checking. Remove it for a proof to count.")
                return Result(Verdict.UNKNOWN, (output + "\n" + note).strip(), details)
            if _NATIVE_RE.search(masked):
                note = ("`native_decide` / `decide +native` / `ofReduceBool` trust compiled code instead of the "
                        "kernel and are not accepted as proof; use `decide`, `norm_num` or `simp`.")
                return Result(Verdict.ERROR, (output + "\n" + note).strip(), details)
            problem = _audit(d, env, deadline)
            if problem is not None:
                verdict, note = problem
                details["audit"] = note
                return Result(verdict, (output + "\n" + note).strip(), details)
        return Result(
            Verdict.PROVED,
            output or "no errors, no sorry; the kernel re-checked every declaration and they use only standard axioms",
            details,
        )

    def _sorry_goals(self, code: str, timeout: float) -> list:
        """The goal at each `sorry`, in order, via the REPL (best effort)."""
        header, body, _ = _split_header(code)
        repl = self.pool.get(header)
        try:
            with repl.lock:
                for attempt in (1, 2):  # restart a REPL that died since its last use, once
                    if repl.ensure(max(timeout, 120)):
                        return []
                    try:
                        resp = repl.command({"cmd": body}, timeout)
                        break
                    except RuntimeError:
                        if attempt == 2:
                            raise
        except (TimeoutError, RuntimeError):
            return []
        return [s.get("goal", "") for s in resp.get("sorries", [])]

    # -- sessions ---------------------------------------------------------------------

    def start(self, code: str, timeout: float) -> Result:
        holes = list(_HOLE_RE.finditer(_mask(code)))
        if len(holes) != 1:
            return Result(
                Verdict.ERROR,
                f"a session needs exactly one `sorry` marking where the steps go; found {len(holes)}.",
                {"goals": []},
            )
        axioms = _AXIOM_RE.findall(_mask(code))
        if axioms:
            return Result(Verdict.ERROR, f"axiom declarations are not allowed: {', '.join(axioms)}", {"goals": []})
        header, body, offset = _split_header(code)
        repl = self.pool.get(header)
        try:
            with repl.lock:
                for attempt in (1, 2):  # a REPL that died since its last use is restarted once
                    header_errors = repl.ensure(max(timeout, 120))
                    if header_errors:
                        return Result(Verdict.ERROR, _fmt(header_errors), {"messages": header_errors, "goals": []})
                    try:
                        resp = repl.command({"cmd": body}, timeout)
                        break
                    except RuntimeError:
                        if attempt == 2:
                            raise
                generation = repl.generation
        except TimeoutError:
            return Result(Verdict.UNKNOWN, "elaboration timed out", {"timeout": True, "goals": []})
        except RuntimeError as e:
            return Result(Verdict.ERROR, str(e), {"goals": []})
        messages = [_message(m) for m in resp.get("messages", [])]
        for m in messages:
            m["line"] = (m["line"] or 0) + offset
        if "message" in resp:
            return Result(Verdict.ERROR, _clean(resp["message"]), {"goals": []})
        if any(m["severity"] == "error" for m in messages):
            return Result(Verdict.ERROR, _fmt(messages), {"messages": messages, "goals": _unsolved_goals(messages)})
        sorries = resp.get("sorries", [])
        if len(sorries) != 1:
            return Result(
                Verdict.ERROR,
                f"the `sorry` was elaborated into {len(sorries)} proof states; put it where it stands for exactly one goal.",
                {"goals": [s.get("goal", "") for s in sorries]},
            )
        hole = _Hole(code, holes[0].start(), holes[0].end())
        goal = sorries[0].get("goal", "")
        state = self._mint(_State(repl, generation, sorries[0]["proofState"], hole, ()))
        return Result(Verdict.UNKNOWN, f"session started; 1 goal:\n{goal}", {"state": state, "goals": [goal]})

    def step(self, state: str, step: str, timeout: float) -> Result:
        with self.states_lock:
            st = self.states.get(state)
        if st is None:
            return Result(Verdict.ERROR, f"unknown or expired state {state!r}; start a new session.", {"goals": []})
        tactic = step.replace("\r\n", "\n").strip("\n").rstrip()
        if not tactic.strip():
            return Result(Verdict.ERROR, "empty step", {"goals": []})
        repl = st.repl
        try:
            with repl.lock:
                if not repl.alive or repl.generation != st.generation:
                    return Result(Verdict.ERROR, f"unknown or expired state {state!r}; start a new session.", {"goals": []})
                resp = repl.command({"tactic": tactic, "proofState": st.proof_state}, timeout)
        except TimeoutError:
            return Result(
                Verdict.UNKNOWN,
                "the step timed out; the Lean session was reset, so start a new session.",
                {"timeout": True, "goals": []},
            )
        except RuntimeError as e:
            return Result(Verdict.ERROR, f"{e}; start a new session.", {"goals": []})
        errors = [_message(m) for m in resp.get("messages", []) if m.get("severity") == "error"]
        if "message" in resp or errors or "proofState" not in resp:
            text = _clean(resp["message"]) if "message" in resp else _fmt(errors) or str(resp)
            return Result(Verdict.ERROR, text, {"goals": []})
        path = st.path + (tactic,)
        goals = resp.get("goals") or []
        if goals:
            new = self._mint(_State(repl, st.generation, resp["proofState"], st.hole, path))
            listing = "\n\n".join(goals)
            return Result(
                Verdict.UNKNOWN,
                f"{len(goals)} goal{'s' * (len(goals) != 1)} left:\n{listing}",
                {"state": new, "goals": goals, "path": list(path)},
            )
        return self._check(st.hole, path, timeout)

    def _check(self, hole: _Hole, path: tuple, timeout: float) -> Result:
        """No goals left: assemble the whole file and let a fresh `lean` + kernel decide."""
        first: Optional[Result] = None
        for text in _assemblies(hole, path):
            result = self.run(text, timeout, challenge=hole.code)  # the session's statement is the challenge
            if result.verdict is Verdict.PROVED:
                result.output = f"all goals closed; the assembled proof was checked by the kernel:\n\n{text}"
                result.details.update(proof=text, path=list(path), goals=[])
                return result
            if first is None:
                first = result
                first.details.update(assembled=text, path=list(path))
            if result.verdict is not Verdict.ERROR:
                break
        assert first is not None
        first.output = (
            "the session closed all goals, but the assembled proof is not accepted as a complete proof:\n"
            + first.output
        )
        return first

    def _mint(self, st: _State) -> str:
        key = uuid.uuid4().hex[:16]
        with self.states_lock:
            self.states[key] = st
            while len(self.states) > MAX_STATES:
                self.states.popitem(last=False)
        return key


# -- certification with Lake's comparator ------------------------------------------------

STANDARD_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
_DECL_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:private|protected|noncomputable|nonrec|partial)[ \t]+)*"
    r"(theorem|lemma|def|abbrev)[ \t]+([^\s(:{\[]+)", re.M)  # fmt: skip
_SCOPE_RE = re.compile(r"^[ \t]*(namespace|section|end)\b[ \t]*([^\s]*)", re.M)


def _holes_named(code: str) -> tuple:
    """(theorem names, definition names) of the declarations in ``code`` whose body has a ``sorry``."""
    masked = _mask(code)
    events = sorted([(m.start(), "scope", m.group(1), m.group(2)) for m in _SCOPE_RE.finditer(masked)]
                    + [(m.start(), "decl", m.group(1), m.group(2)) for m in _DECL_RE.finditer(masked)])  # fmt: skip
    decl_starts = [pos for pos, kind, *_ in events if kind == "decl"] + [len(masked)]
    scopes: list = []
    theorems, definitions = [], []
    for pos, kind, word, name in events:
        if kind == "scope":
            if word == "end":
                if scopes:
                    scopes.pop()
            else:
                scopes.append(name if word == "namespace" else None)
            continue
        body = masked[pos : next(p for p in decl_starts if p > pos)]
        if not re.search(r"(?<![\w.'])sorry(?![\w'])", body):
            continue
        prefix = ".".join(part for part in scopes if part)
        full = name[len("_root_."):] if name.startswith("_root_.") else f"{prefix}.{name}" if prefix else name
        (theorems if word in ("theorem", "lemma") else definitions).append(full)
    return theorems, definitions


def _cert_project(d) -> None:
    """A throwaway Lake project in ``d`` that reuses the prebuilt Mathlib read-only."""
    project_toml = open(os.path.join(PROJECT, "lakefile.toml")).read().split("\n", 1)[1]
    head = 'name = "cert"\n'
    libs = "".join(f'\n[[lean_lib]]\nname = "{m}"\n' for m in ("Challenge", "Solution"))
    with open(os.path.join(d, "lakefile.toml"), "w") as f:
        f.write(head + project_toml + libs)
    with open(os.path.join(PROJECT, "lake-manifest.json")) as src, open(os.path.join(d, "lake-manifest.json"), "w") as dst:
        dst.write(src.read())
    os.makedirs(os.path.join(d, ".lake"), exist_ok=True)
    os.symlink(os.path.join(PROJECT, ".lake", "packages"), os.path.join(d, ".lake", "packages"))


def _certify(solution: str, proved: Result, challenge: str, paranoid: bool, timeout: float) -> Result:
    """Certify a would-be proof against its challenge with ``lake comparator`` (Lean >= 4.35).

    Every theorem the challenge leaves as ``sorry`` must be proved in the solution with the
    same statement, using only the standard axioms, and be accepted by the kernel; the
    untrusted file is built inside Lake's bubblewrap sandbox, as Lake's documentation
    prescribes. If certification cannot run, the result is unknown - never a silent "proved".
    (Files without a challenge keep the kernel replay and axiom audit of ``run``; ``lake
    check`` would replay all of Mathlib for every such file.)
    """
    theorems, definitions = _holes_named(challenge)
    if not theorems and not definitions:
        return Result(Verdict.ERROR, "the challenge has no theorem or definition left as `sorry` to prove",
                      proved.details, proved.backend)  # fmt: skip
    with workdir({"Solution.lean": solution, "Challenge.lean": challenge}) as d:
        _cert_project(str(d))
        config = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": theorems,
                  "definition_names": definitions, "permitted_axioms": STANDARD_AXIOMS}  # fmt: skip
        (d / "comparator.json").write_text(json.dumps(config))
        cmd = ["lake", "comparator"] + (["--paranoid"] if paranoid else [])
        runtime = f"/run/user/{os.getuid()}"
        os.makedirs(runtime, exist_ok=True)
        toolchain_bin = os.path.dirname(shutil.which("lean") or "/usr/bin/lean")
        proc = sh(cmd, cwd=d, timeout=timeout, env={"XDG_RUNTIME_DIR": runtime, "PATH": f"{toolchain_bin}:{os.environ.get('PATH', '')}"})
    tool = " ".join(cmd)
    details = dict(proved.details)
    if proc.timed_out:
        details["certified"] = False
        return Result(Verdict.UNKNOWN, f"{proved.output}\n\nnot certified: `{tool}` did not finish in time", details,
                      proved.backend)  # fmt: skip
    report = "\n".join(line for line in proc.out.splitlines()
                       if re.search(r"error|okay|accept|reject|not permitted|Illegal|match", line, re.I))[-2000:]  # fmt: skip
    if proc.returncode == 0:
        details["certified"] = {"tool": tool, "theorems": theorems, "definitions": definitions,
                                "permitted_axioms": STANDARD_AXIOMS, "paranoid": paranoid}  # fmt: skip
        if definitions:  # definition holes can be gamed (see Lake's comparator docs): flag for review
            details["needs_review"] = definitions
        note = f"certified by `{tool}`" + (f" (definition holes {definitions} need review)" if definitions else "")
        return Result(Verdict.PROVED, f"{proved.output}\n{note}".strip(), details, proved.backend)
    details["certified"] = False
    if proc.returncode == 1:  # rejected: wrong statement, forbidden axiom, kernel rejection or failed build
        return Result(Verdict.ERROR, f"`{tool}` rejected the proof:\n{report or proc.out[-2000:]}", details,
                      proved.backend)  # fmt: skip
    return Result(Verdict.UNKNOWN, f"{proved.output}\n\nnot certified: `{tool}` could not start:\n{proc.out[-1500:]}",
                  details, proved.backend)  # fmt: skip


def _clean(message: str) -> str:
    return message.replace("Lean error:\n", "", 1).strip()


ADAPTER = Lean()
