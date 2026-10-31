"""Line-located error messages for adapters whose tools report "line N" in text.

``details["messages"]`` - a list of ``{"severity", "line", "message"}`` - is
what location-aware patterns read: ``patterns.repair`` / ``localize`` show
the failing lines, ``learn.prefix_labels`` labels proof/program prefixes
by the first error. Decorate an adapter's ``run`` with :func:`locates` to
derive them from its own ERROR output when it does not set them itself.
"""

from __future__ import annotations

import functools
import re
from typing import Callable, Dict, List

from formalkit.core import Result, Verdict

# "line 12:", "line 12, col 3", "[Line: 12]", "main.c:12:", 'File "model.py", line 12'
_LINE = re.compile(r"(?:\bline[: ]\s*|\[Line: |\bmain\.c:|model\.py\", line )(\d+)", re.IGNORECASE)


def error_messages(text: str, skip: tuple = ()) -> List[Dict]:
    """One message per output line that names a source line (lines containing a ``skip`` marker excluded)."""
    out = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or any(s in line for s in skip):
            continue
        m = _LINE.search(line)
        if m:
            out.append({"severity": "error", "line": int(m.group(1)), "message": line})
    return out


def locates(skip: tuple = ()) -> Callable:
    """Decorator for ``Adapter.run``: attach ``details["messages"]`` to ERROR results."""

    def wrap(run: Callable) -> Callable:
        @functools.wraps(run)
        def inner(self, code: str, timeout: float, **inputs: str) -> Result:
            result = run(self, code, timeout, **inputs)
            if result.verdict is Verdict.ERROR and "messages" not in result.details:
                messages = error_messages(result.output, skip)
                if messages:
                    result.details["messages"] = messages
            return result

        return inner

    return wrap
