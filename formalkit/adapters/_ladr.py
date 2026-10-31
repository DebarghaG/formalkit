"""Shared parsing for LADR tools (Prover9, Mace4)."""

from __future__ import annotations

import re

_SECTION_RE = re.compile(r"^={5,} ([A-Z][A-Z ]*?) ={5,}$(.*?)(?=^={5,} )", re.S | re.M)
_GOALS_RE = re.compile(r"^\s*formulas\(goals\)\.", re.M)


def sections(out: str) -> list[tuple[str, str]]:
    """``(title, body)`` for each ``===== TITLE =====`` section, in order."""
    return [(title.strip(), body.strip("\n")) for title, body in _SECTION_RE.findall(out + "\n===== END =====")]


def errors(out: str) -> str:
    """The error lines (stdout and stderr both repeat them, so dedupe)."""
    keep = ("%%ERROR", "%%START ERROR", "Fatal error")
    lines = [line.strip() for line in out.splitlines() if line.strip().startswith(keep)]
    return "\n".join(dict.fromkeys(lines))


def has_goals(code: str) -> bool:
    return bool(_GOALS_RE.search(code))


_GOALS_BODY_RE = re.compile(r"formulas\(goals\)\.(.*?)end_of_list\.", re.S)


def goal_count(code: str) -> int:
    """Number of goal formulas (comments and attributes ignored)."""
    total = 0
    for body in _GOALS_BODY_RE.findall(code):
        body = re.sub(r"%[^\n]*", "", body)
        total += len([g for g in re.split(r"\.(?=\s|$)", body) if g.split("#", 1)[0].strip()])
    return total
