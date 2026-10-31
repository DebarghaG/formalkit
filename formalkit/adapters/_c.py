"""Shared helpers for the C program verifiers (cbmc, esbmc, framac, ultimate).

Verifier options travel inside the program as a comment line, so the tool
interface stays a single ``code`` string:

    // cbmc: --unwind 10 --signed-overflow-check

Only whitelisted options are accepted; options that would make a PROVED
verdict dishonest (e.g. disabling unwinding assertions) are refused.
"""

from __future__ import annotations

import re
import shlex
from typing import Dict, List, Optional, Tuple

# The one-line verdict summary each adapter prints first.
HEADLINE = {
    "proved": "VERIFICATION SUCCESSFUL",
    "refuted": "VERIFICATION FAILED",
    "unknown": "VERIFICATION INCONCLUSIVE",
    "error": "INPUT REJECTED",
}


def options(code: str, tool: str, allowed: Dict[str, bool]) -> Tuple[List[str], Optional[str]]:
    """Collect ``// <tool>: ...`` options from ``code``.

    ``allowed`` maps an option name to whether it takes a value; a key
    starting with ``*`` matches by suffix, so ``"*-check"`` admits every
    ``--...-check`` flag. Returns ``(args, error)``, where ``error`` is a
    message for the model if an option is not allowed.
    """
    args: List[str] = []
    pattern = re.compile(r"^\s*//\s*" + re.escape(tool) + r"\s*:(.*)$")
    for line in code.splitlines():
        m = pattern.match(line)
        if not m:
            continue
        try:
            tokens = shlex.split(m.group(1))
        except ValueError as e:
            return [], f"could not parse '// {tool}:' options: {e}"
        i = 0
        while i < len(tokens):
            tok = tokens[i]
            name, eq, value = tok.partition("=")
            takes = _lookup(name, allowed)
            if takes is None:
                return [], (
                    f"option {name!r} is not allowed in '// {tool}:' lines. "
                    f"Allowed: {', '.join(sorted(allowed))}"
                )
            args.append(name)
            if takes:
                if eq:
                    args.append(value)
                elif i + 1 < len(tokens):
                    i += 1
                    args.append(tokens[i])
                else:
                    return [], f"option {name!r} needs a value"
            i += 1
    return args, None


def _lookup(name: str, allowed: Dict[str, bool]) -> Optional[bool]:
    if name in allowed:
        return allowed[name]
    for key, takes in allowed.items():
        if key.startswith("*") and name.startswith("--") and name.endswith(key[1:]):
            return takes
    return None


def has_option(args: List[str], *names: str) -> bool:
    return any(a in names for a in args)


def disabled_checks(args: List[str]) -> List[str]:
    """Options among ``args`` that switch checks off (``--no-...``, ``-wp-no-rte``)."""
    return [a for a in args if a.startswith("--no-") or a == "-wp-no-rte"]


def qualify(result, args: List[str]):
    """Say, on a PROVED result, which checks the options switched off (a proof covers only what was checked)."""
    off = disabled_checks(args)
    if off and result.verdict.value == "proved":
        result.details["unchecked"] = off
        result.output += f"\nNote: checks disabled by options were not verified: {', '.join(off)}."
    return result
