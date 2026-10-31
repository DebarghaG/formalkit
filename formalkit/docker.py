"""Container lifecycle via the ``docker`` CLI: build, up, down, status.

One long-lived container per backend, named ``formalkit-<backend>`` and
published on a random localhost port. ``up`` is idempotent: it reuses a
running container, so many processes can share one warm backend.

Environment knobs:
    FORMALKIT_IMAGE_PREFIX   image name prefix (default ``formalkit/``)
    FORMALKIT_MEMORY         per-container memory limit (default ``8g``)
    FORMALKIT_DOCKER_ARGS    extra ``docker run`` args, e.g. a license mount
"""

from __future__ import annotations

import json
import os
import shlex
import subprocess
import sys
import time
import urllib.request
from pathlib import Path

from formalkit.registry import entry

ROOT = Path(__file__).resolve().parent.parent
PORT = 8080


class DockerError(RuntimeError):
    pass


def _docker(*args: str, check: bool = True, capture: bool = True) -> str:
    try:
        proc = subprocess.run(["docker", *args], capture_output=capture, text=True)
    except FileNotFoundError:
        raise DockerError("the docker CLI is not installed or not on PATH") from None
    if check and proc.returncode != 0:
        raise DockerError(f"docker {' '.join(args[:2])} failed:\n{(proc.stderr or '').strip()}")
    return (proc.stdout or "").strip()


def image(name: str) -> str:
    return f"{os.environ.get('FORMALKIT_IMAGE_PREFIX', 'formalkit/')}{entry(name).image}:latest"


def container(name: str) -> str:
    return f"formalkit-{name}"


def dockerfile(name: str) -> Path:
    return ROOT / "docker" / entry(name).image / "Dockerfile"


def has_image(name: str) -> bool:
    return bool(_docker("images", "-q", image(name), check=False))


def build(name: str, *, quiet: bool = False, pull: bool = False) -> str:
    """Build a backend's image from ``docker/<image>/Dockerfile``."""
    path = dockerfile(name)
    if not path.exists():
        raise DockerError(f"no Dockerfile for {name!r} at {path}; install formalkit from source to build images")
    args = ["build", "-t", image(name), "-f", str(path), str(ROOT)]
    if pull:
        args.insert(1, "--pull")
    if quiet:
        args.insert(1, "-q")
    _docker(*args, capture=quiet)
    return image(name)


def _inspect(name: str) -> dict | None:
    out = _docker("inspect", container(name), check=False)
    data = json.loads(out) if out.startswith("[") else []
    return data[0] if data else None


def url(name: str) -> str | None:
    """URL of a running backend container, or None."""
    info = _inspect(name)
    if not info or not info["State"]["Running"]:
        return None
    bindings = (info["NetworkSettings"]["Ports"] or {}).get(f"{PORT}/tcp") or []
    if not bindings:
        return None
    return f"http://127.0.0.1:{bindings[0]['HostPort']}"


def _wait_healthy(base: str, name: str, timeout: float = 60) -> None:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        try:
            with urllib.request.urlopen(f"{base}/health", timeout=2) as r:
                if r.status == 200:
                    return
        except OSError:
            info = _inspect(name)
            if not info or not info["State"]["Running"]:
                break  # the server died (e.g. an import error): fail fast
            time.sleep(0.25)
    logs = _docker("logs", "--tail", "30", container(name), check=False)
    raise DockerError(f"backend {name!r} did not become healthy at {base}:\n{logs}")


def up(name: str, *, build_missing: bool = True, _retry: bool = True) -> str:
    """Start (or reuse) a backend container and return its URL."""
    if existing := url(name):
        return existing
    if _inspect(name):  # stopped / broken leftover
        _docker("rm", "-f", container(name), check=False)
    if not has_image(name):
        if not build_missing:
            raise DockerError(f"image {image(name)} not found; run `formalkit build {name}`")
        print(f"[formalkit] building {image(name)} (first use; this can take a while)...", file=sys.stderr, flush=True)
        build(name)
    try:
        _docker(
            "run", "-d", "--init", "--name", container(name),
            "-p", f"127.0.0.1::{PORT}",
            "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
            "--pids-limit", "4096",
            "--memory", os.environ.get("FORMALKIT_MEMORY", "8g"),
            "--label", "formalkit=1",
            *entry(name).docker_args,
            *shlex.split(os.environ.get("FORMALKIT_DOCKER_ARGS", "")),
            image(name), "python3", "-m", "formalkit.server", name,
        )  # fmt: skip
    except DockerError as e:
        if "already in use" not in str(e):
            raise  # another process creating it at the same moment is fine: we reuse theirs
    for _ in range(40):  # port binding appears shortly after start
        if base := url(name):
            try:
                _wait_healthy(base, name)
            except DockerError:
                if _inspect(name) or not _retry:
                    raise
                return up(name, build_missing=build_missing, _retry=False)  # another process removed it meanwhile
            return base
        time.sleep(0.25)
    logs = _docker("logs", "--tail", "30", container(name), check=False)
    raise DockerError(f"backend {name!r} exited during startup:\n{logs}")


def down(name: str) -> None:
    _docker("rm", "-f", container(name), check=False)


def running() -> list[str]:
    """Names of running formalkit backends."""
    out = _docker("ps", "--filter", "label=formalkit=1", "--format", "{{.Names}}", check=False)
    return sorted(n.removeprefix("formalkit-") for n in out.split() if n)
