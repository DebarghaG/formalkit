from __future__ import annotations

import os
import re
import signal
import threading
import time
import uuid

from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

_COMMENT_RE = re.compile(r"\(\*.*?\*\)", re.S)
_THEORY_RE = re.compile(r"^\s*theory\s+\"?([A-Za-z][\w']*)\"?", re.M)
_CHEAT_RE = re.compile(r"\b(sorry|oops)\b")
_AXIOM_RE = re.compile(r"\b(axiomatization|axioms)\b")
_HEADER_RE = re.compile(r'^(\w[\w ]*?) \(line (\d+) of "[^"]*"\):$', re.M)
_COUNTEREXAMPLE_RE = re.compile(r"(Nitpick|Quickcheck) found a (?:potential )?counterexample", re.I)
_GOAL_HEAD_RE = re.compile(r"\bgoal \(\d+ subgoals?\):")
_SUBGOAL_RE = re.compile(r"^\s*\d+\.\s(.*)$")
# Commands and methods that run arbitrary ML can forge theorems (oracles, Skip_Proof.cheat_tac):
# not accepted, so that a proof is always a proof.
_ML_RE = re.compile(
    r"(?<![\w.'])(ML|ML_val|ML_prf|ML_file|ML_command|SML_file|setup|local_setup|declaration|syntax_declaration|"
    r"method_setup|attribute_setup|oracle|simproc_setup|parse_translation|print_translation|"
    r"parse_ast_translation|print_ast_translation|typed_print_translation)(?![\w.'])(?!\s*:)"
    r"|\(\s*(raw_)?tactic\b|\btactic\s*\\<open>",
)  # anywhere, not just at line starts: Isabelle allows several commands on one line
_LIBRARY_RE = re.compile(r'"?HOL-Library\.')
_CLAIM_RE = re.compile(r"^\s*(lemma|theorem|corollary|proposition|schematic_goal|interpretation|instance)\b", re.M)
_OPEN, _CLOSE = "\\<open>", "\\<close>"


_TAG = "FORMALKIT_RUN"


def _kill_tagged(tag: str) -> None:
    """Kill every process started for one run.

    Isabelle launches Poly/ML (and helpers) in sessions of their own, so
    killing our process group on a timeout leaves the prover running - a
    looping `simp` would burn a CPU forever. Every descendant inherits the
    run's tag in its environment, wherever it was reparented to.
    """
    marker = f"{_TAG}={tag}".encode()
    for entry in os.listdir("/proc"):
        if not entry.isdigit() or int(entry) == os.getpid():
            continue
        try:
            with open(f"/proc/{entry}/environ", "rb") as f:
                if marker in f.read().split(b"\0"):
                    os.kill(int(entry), signal.SIGKILL)
        except (OSError, ValueError):
            continue


def _mask_strings(text: str) -> str:
    """Blank the inside of "..." strings (inner-syntax terms), keeping quotes and newlines."""
    out, i, n = list(text), 0, len(text)
    while i < n:
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            for k in range(i + 1, min(j, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j + 1
        else:
            i += 1
    return "".join(out)


def _mask_cartouches(text: str) -> str:
    """Blank the inside of (nested) cartouches, keeping the delimiters and newlines.

    Document text such as ``text \\<open>... sorry ...\\<close>`` must not count as a
    `sorry`, and its lines must not look like commands.
    """
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith(_OPEN, i):
            depth += 1
            out.append(_OPEN)
            i += len(_OPEN)
        elif text.startswith(_CLOSE, i) and depth:
            depth -= 1
            out.append(_CLOSE)
            i += len(_CLOSE)
        else:
            out.append(text[i] if depth == 0 or text[i] == "\n" else " ")
            i += 1
    return "".join(out)
# Each check runs a JVM plus a Poly/ML process (GBs each): bound how many run at once.
_JOBS = threading.BoundedSemaphore(int(os.environ.get("FORMALKIT_ISABELLE_JOBS", "2")))


class Isabelle(Adapter):
    spec = Spec(
        version="Isabelle2026",
        name="isabelle",
        timeout=120,
        family="Interactive theorem prover",
        language="Isabelle/HOL theory (.thy)",
        emits="theories, Isar proofs, tactic calls.",
        authority="higher-order logic checked by an LCF-style kernel.",
        feedback="errors with the remaining subgoals, output of sledgehammer (proof suggestions), nitpick and quickcheck (counterexamples).",
        use="large structured developments, proof repair.",
        guidance=(
            "Send one complete theory: `theory Scratch imports Main begin ... end` (any theory name; Main/HOL "
            "is preloaded; HOL-Library theories may be imported as \"HOL-Library.Name\"). "
            "Verdicts: proved = the theory checked with no errors and no `sorry`/`oops`; error = Isabelle rejected "
            "something (messages include the failing command and the remaining subgoals); unknown = the theory checks "
            "but contains `sorry` or `oops` (incomplete); refuted = `nitpick` or `quickcheck` found a counterexample "
            "to a lemma - write `lemma ... nitpick oops` to test a conjecture. `axiomatization` and ML-level commands "
            "or tactics (ML, setup, oracle, (tactic ...)) are rejected. "
            "Use `sledgehammer` inside a proof to get suggested one-line proofs, then paste one in."
        ),
        example=(
            "theory Scratch imports Main begin\n\nlemma rev_rev: \"rev (rev xs) = xs\"\n  by simp\n\n"
            "lemma \"length (xs @ ys) = length xs + length ys\"\n  by (induct xs) auto\n\nend"
        ),
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        deadline = time.monotonic() + timeout
        source = _mask_cartouches(_COMMENT_RE.sub(" ", code))
        match = _THEORY_RE.search(source)
        if not match:
            return Result(Verdict.ERROR, "expected a theory header: theory Scratch imports Main begin ... end")
        name = match.group(1)
        cheats = sorted(set(_CHEAT_RE.findall(source)))
        details = {"theory": name, "incomplete": cheats}
        if _AXIOM_RE.search(source):
            return Result(Verdict.ERROR, "axiomatization is not allowed (axioms can prove anything)", details)
        ml = _ML_RE.search(_mask_strings(source))
        if ml:
            return Result(Verdict.ERROR, f"ML-level commands and tactics are not allowed (they can forge theorems): "
                                         f"{ml.group(0).strip()}", details)  # fmt: skip
        logic = "HOL-Library" if _LIBRARY_RE.search(source) else "HOL"
        # Strict by default. Only when the theory has `sorry`/`oops` do we turn on
        # quick_and_dirty, so the rest is still checked; it is then reported as incomplete.
        options = ["-o", "quick_and_dirty"] if cheats else []
        if not _JOBS.acquire(timeout=max(0.0, deadline - time.monotonic())):
            return Result(Verdict.UNKNOWN, "Isabelle is busy with other checks; try again.", {**details, "timeout": True})
        try:
            tag = uuid.uuid4().hex
            try:
                with workdir({f"{name}.thy": code}) as d:
                    proc = sh(
                        ["isabelle", "process_theories", "-l", logic, *options, "-O", "-f", f"{name}.thy", name],
                        cwd=d,
                        timeout=max(1.0, deadline - time.monotonic()),
                        env={_TAG: tag},
                    )
            finally:
                _kill_tagged(tag)
        finally:
            _JOBS.release()
        if proc.timed_out:
            return timed_out(proc)
        output = proc.out.replace("Draft/", "").replace("Running Draft ...", "").strip()
        details["messages"] = _messages(output)
        details["goals"] = _goals(details["messages"])
        if proc.returncode != 0 and re.search(r"\bKilled\b", output) and not any(
            m["severity"] == "error" for m in details["messages"]
        ):
            return Result(Verdict.UNKNOWN, "Isabelle was killed (out of memory); not checked.\n" + output, details)
        if proc.returncode != 0:
            return Result(Verdict.ERROR, output or f"isabelle exited with code {proc.returncode}", details)
        if _COUNTEREXAMPLE_RE.search(output):
            return Result(Verdict.REFUTED, output, details)
        if cheats:
            note = f"theory checks but is incomplete: uses {', '.join(cheats)}"
            return Result(Verdict.UNKNOWN, (output + "\n" + note).strip(), details)
        if not _CLAIM_RE.search(source):
            note = "nothing was proved: the theory states no lemma or theorem."
            return Result(Verdict.UNKNOWN, (output + "\n" + note).strip(), details)
        return Result(Verdict.PROVED, output or f"theory {name} checked: all proofs accepted by the kernel", details)


def _messages(output: str) -> list:
    """Split process_theories output into {severity, line, message} records."""
    heads = list(_HEADER_RE.finditer(output))
    out = []
    for i, m in enumerate(heads):
        end = heads[i + 1].start() if i + 1 < len(heads) else len(output)
        body = output[m.end() : end].strip()
        if i + 1 == len(heads):  # the build summary follows the last message
            body = body.split("\nFinished Draft", 1)[0].split("\nDraft FAILED", 1)[0]
        out.append({"severity": m.group(1).lower(), "line": int(m.group(2)), "message": body.strip()})
    return out


def _goals(messages: list) -> list:
    """Remaining subgoals reported by errors ("goal (n subgoals): 1. ... 2. ...")."""
    goals: list = []
    for m in messages:
        if m["severity"] != "error":
            continue
        in_goal = False
        for raw in m["message"].splitlines():
            line = raw[3:] if raw.startswith("***") else raw
            if _GOAL_HEAD_RE.search(line):
                in_goal = True
                continue
            if not in_goal:
                continue
            item = _SUBGOAL_RE.match(line)
            if item:
                goals.append(item.group(1).strip())
            elif goals and line.startswith("   ") and line.strip():
                goals[-1] += " " + line.strip()  # a subgoal wrapped over several lines
            else:
                in_goal = False
    return goals


ADAPTER = Isabelle()
