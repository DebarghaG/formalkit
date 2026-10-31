"""Integration tests: every file in examples/<backend>/ runs with its expected verdict.

Naming convention:  examples/<backend>/<verdict>-<label>.<ext>
Extra named inputs: examples/<backend>/<verdict>-<label>.<input>.<ext>
e.g. examples/downward/sat-blocks.pddl + examples/downward/sat-blocks.problem.pddl

Backends whose image is not built are skipped. Run with:  pytest -m docker
"""

from __future__ import annotations

from pathlib import Path

import pytest

from formalkit import Verdict, backend, docker
from formalkit.registry import BACKENDS

EXAMPLES = Path(__file__).resolve().parent.parent / "examples"


def _cases():
    for d in sorted(p for p in EXAMPLES.iterdir() if p.is_dir() and p.name in BACKENDS):
        for f in sorted(d.iterdir()):
            stem = f.name.split(".")[0]
            if f.name.count(".") == 1 and stem.split("-")[0] in Verdict._value2member_map_:
                yield pytest.param(d.name, f, id=f"{d.name}/{f.name}")


@pytest.mark.docker
@pytest.mark.parametrize("name,path", list(_cases()))
def test_example(name: str, path: Path) -> None:
    if not docker.has_image(name):
        pytest.skip(f"image for {name} not built")
    stem = path.name.split(".")[0]
    inputs = {f.name.split(".")[1]: f.read_text() for f in path.parent.glob(f"{stem}.*.*")}
    result = backend(name).run(path.read_text(), timeout=120, **inputs)
    assert result.verdict.value == stem.split("-")[0], result.feedback()
