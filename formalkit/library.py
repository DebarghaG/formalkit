"""A library of verified artifacts that grows while you work.

    lib = formalkit.Library()
    lib.add("add_comm'", lemma_code, result)     # admitted only if the backend proved it
    lib.search("a + b = b + a", k=5)             # the most relevant entries
    lean_with_lib = lib.attach(lean)             # a backend whose files see every proved lemma

Admission is by authority: an entry is ``proved`` only when a backend's
Result says so, and that Result is kept as its evidence. Unverified
material (fragments of failed proofs, conjectures) can be stored too,
but always with its real status, and only proved entries are attached.
Retrieval is pluggable; the default ranks by token overlap, which is
crude but dependency-free - plug in embeddings or a premise selector.
"""

from __future__ import annotations

import json
import re
import threading
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Sequence

from formalkit.core import Result, Verdict

_TOKEN = re.compile(r"[A-Za-z_][A-Za-z_0-9'.]*|[^\sA-Za-z_0-9]")


@dataclass
class Entry:
    name: str
    code: str
    status: Verdict  # PROVED for verified entries; anything else is unverified material
    backend: str = ""
    tags: list[str] = field(default_factory=list)

    @property
    def proved(self) -> bool:
        return self.status is Verdict.PROVED


def _tokens(text: str) -> set[str]:
    return set(_TOKEN.findall(text))


def overlap(query: str, entry: Entry) -> float:
    """The default retrieval score: Jaccard overlap of identifier/symbol tokens."""
    a, b = _tokens(query), _tokens(entry.code)
    return len(a & b) / (len(a | b) or 1)


class Library:
    """Verified lemmas, facts and fragments, with retrieval and reuse."""

    def __init__(self, score: Callable[[str, Entry], float] = overlap) -> None:
        self.entries: dict[str, Entry] = {}
        self.score = score
        self._lock = threading.Lock()

    def __len__(self) -> int:
        return len(self.entries)

    def __contains__(self, name: str) -> bool:
        return name in self.entries

    def add(self, name: str, code: str, result: Result, tags: Sequence[str] = ()) -> Entry:
        """Store ``code`` under ``name`` with the status the backend gave it.

        Only a PROVED result makes an entry verified; a proved entry is never
        replaced by an unverified one with the same name.
        """
        entry = Entry(name, code.strip(), result.verdict, result.backend, list(tags))
        with self._lock:
            old = self.entries.get(name)
            if not (old and old.proved and not entry.proved):
                self.entries[name] = entry
        return self.entries[name]

    def proved(self) -> list[Entry]:
        return [e for e in self.entries.values() if e.proved]

    def search(self, query: str, k: int = 5, proved_only: bool = True) -> list[Entry]:
        """The ``k`` entries most relevant to ``query`` (a goal, a statement...)."""
        pool = self.proved() if proved_only else list(self.entries.values())
        ranked = sorted(pool, key=lambda e: self.score(query, e), reverse=True)
        return [e for e in ranked[:k] if self.score(query, e) > 0]

    def context(self, k: int = 5) -> Callable[[str], str]:
        """A ``context`` provider for the LLM patterns: relevant proved entries as text."""

        def provide(query: str) -> str:
            hits = self.search(query, k)
            return "" if not hits else "Proved results you may use:\n\n" + "\n\n".join(e.code for e in hits)

        return provide

    def preamble(self, entries: Sequence[Entry] | None = None) -> str:
        """Proved entries as one file prefix, with ``import`` lines hoisted and deduplicated."""
        imports, bodies = [], []
        for e in self.proved() if entries is None else [x for x in entries if x.proved]:
            for line in e.code.splitlines():
                (imports if line.startswith("import ") else bodies).append(line)
            bodies.append("")
        return "\n".join([*dict.fromkeys(imports), "", *bodies]).strip() + "\n"

    def attach(self, backend):
        """``backend``, with every proved entry prepended to each input.

        Later proofs can use earlier lemmas by name. Imports in the input
        are hoisted above the library, so Lean files stay well-formed.
        """
        from formalkit.client import compiled

        def with_library(code: str) -> str:
            own_imports = [line for line in code.splitlines() if line.startswith("import ")]
            rest = "\n".join(line for line in code.splitlines() if not line.startswith("import "))
            pre = self.preamble()
            lib_imports = [line for line in pre.splitlines() if line.startswith("import ")]
            lib_body = "\n".join(line for line in pre.splitlines() if not line.startswith("import "))
            header = "\n".join(dict.fromkeys(lib_imports + own_imports))
            return f"{header}\n\n{lib_body}\n\n{rest}".strip() + "\n"

        spec = backend.spec
        return compiled(backend, with_library, name=f"{backend.name}_library", language=spec.language,
                        emits=spec.emits, guidance=f"{spec.guidance}\n\nEarlier proved lemmas are available by name.",
                        example=spec.example)  # fmt: skip

    def save(self, path: str | Path) -> None:
        rows = [{"name": e.name, "code": e.code, "status": e.status.value, "backend": e.backend, "tags": e.tags}
                for e in self.entries.values()]  # fmt: skip
        Path(path).write_text("\n".join(json.dumps(r) for r in rows) + "\n")

    @classmethod
    def load(cls, path: str | Path, **kwargs) -> Library:
        lib = cls(**kwargs)
        for line in Path(path).read_text().splitlines():
            if line.strip():
                r = json.loads(line)
                lib.entries[r["name"]] = Entry(r["name"], r["code"], Verdict(r["status"]), r["backend"], r["tags"])
        return lib
