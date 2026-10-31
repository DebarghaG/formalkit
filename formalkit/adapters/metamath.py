from __future__ import annotations

import os
import re

from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

LIB = os.environ.get("METAMATH_LIB", "/opt/metamath")
_COMMENT_RE = re.compile(r"\$\(.*?\$\)", re.S)
_INCLUDE_RE = re.compile(r"\$\[\s*(\S+)\s*\$\]")
_STMT_RE = re.compile(r"(\S+)\s+\$([pa])\s+(\S+)")
# metamath-exe reports problems as "?Error ..." / "?Warning ..." blocks.
_PROBLEM_RE = re.compile(r"^\?(Error|Warning)", re.M)
_INCOMPLETE_RE = re.compile(r"were not proved:\s*(.*)|Proof of \"(\S+)\" is incomplete")
_NOISE_RE = re.compile(
    r"Metamath - Version|MM>|Continuous scrolling|Screen width|Reading (?:source|included) file|\d+ bytes were read"
    r"|The source has|No errors were found\.  However|0 10%|\.+$|\s*$"
)


class Metamath(Adapter):
    spec = Spec(
        version="metamath-exe 0.198, set.mm @a1556693",
        name="metamath",
        family="Interactive theorem prover",
        language="Metamath (.mm database)",
        emits="fully explicit proof steps.",
        authority="a minimal verifier (metamath-exe) with no automation.",
        feedback="step-level verification failures: the failing statement, the step, and the expected vs. actual expression.",
        use="fine-grained proof-step generation.",
        guidance=(
            "Send a Metamath database. Either (a) self-contained: declare $c/$v/$f/$a yourself and add $p "
            "theorems; or (b) start with `$[ set.mm $]` to build on the set.mm library, then add only $p theorems "
            "(and $e hypotheses / ${ $} blocks). With set.mm, new `$a` statements (axioms and syntax) are rejected "
            "and only your own $p theorems are verified. "
            "Verdicts: proved = every $p proof in your input verifies; error = parse or verification failure "
            "(messages name the theorem and step); unknown = a proof is incomplete (contains `?`). "
            "Proofs may be uncompressed (label lists) or compressed."
        ),
        example=(
            "$c ( ) -> wff |- $.\n$v p q $.\nwp $f wff p $.\nwq $f wff q $.\n"
            "wi $a wff ( p -> q ) $.\n${ min $e |- p $.\n maj $e |- ( p -> q ) $.\n mp $a |- q $. $}\n"
            "${ h1 $e |- p $.\n h2 $e |- ( p -> q ) $.\n th $p |- q $= wp wq h1 h2 mp $. $}"
        ),
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        stripped = _COMMENT_RE.sub(" ", code)
        includes = _INCLUDE_RE.findall(stripped)
        unknown = [f for f in includes if f != "set.mm"]
        if unknown:
            return Result(Verdict.ERROR, f"only `$[ set.mm $]` can be included, not: {', '.join(unknown)}")
        stmts = _STMT_RE.findall(stripped)
        theorems = [label for label, kind, _ in stmts if kind == "p"]
        details = {"theorems": theorems, "library": "set.mm" if includes else None}
        if includes:
            # Any new $a on top of set.mm is rejected: `|-` axioms prove anything, and new syntax
            # axioms can make the grammar ambiguous, which also breaks soundness.
            new_axioms = [label for label, kind, tc in stmts if kind == "a"]
            if new_axioms:
                return Result(
                    Verdict.ERROR,
                    f"new `$a` axioms are not allowed on top of set.mm (they can prove anything or make the grammar "
                    f"ambiguous): {', '.join(new_axioms)}",
                    details,
                )
            if not theorems:
                return Result(Verdict.ERROR, "no $p theorems to verify", details)
            targets = theorems
        else:
            targets = ["*"]
        commands = ["set scroll continuous", "set width 200", 'read "input.mm"']
        commands += [f"verify proof {t}" for t in targets] + ["exit"]
        if not code.endswith("\n"):
            code += "\n"  # metamath warns about an incomplete last line otherwise
        with workdir({"input.mm": code}) as d:
            if includes:
                os.symlink(os.path.join(LIB, "set.mm"), d / "set.mm")
            proc = sh(["metamath", *commands], cwd=d, timeout=timeout)
        if proc.timed_out:
            return timed_out(proc)
        # Keep only the verifier's findings, not the banner and command echo.
        lines = [ln for ln in proc.out.splitlines() if not _NOISE_RE.match(ln) and ln.strip() not in theorems]
        output = "\n".join(lines).strip()
        errors = [m for m in _PROBLEM_RE.finditer(output) if m.group(1) == "Error"]
        incomplete = [x for a, b in _INCOMPLETE_RE.findall(output) for x in (a + " " + b).split()]
        details["incomplete"] = incomplete
        if incomplete:
            details["goals"] = [f"{label}: proof has unknown (?) steps" for label in incomplete]
        if errors:
            return Result(Verdict.ERROR, output, details)
        if incomplete:
            return Result(Verdict.UNKNOWN, output, details)
        if not includes and not theorems:
            return Result(Verdict.ERROR, (output + "\nno $p theorems to verify").strip(), details)
        summary = f"verified {len(theorems)} theorem(s): {', '.join(theorems)}"
        return Result(Verdict.PROVED, (output + "\n" + summary).strip(), details)


ADAPTER = Metamath()
