"""Container side: the Adapter base class and the HTTP server around it.

Each backend container runs ``python3 -m formalkit.server <name>``, which
imports ``formalkit.adapters.<name>``, takes its ``ADAPTER`` object, and
serves three endpoints:

    GET  /health  -> {"ok": true}
    GET  /spec    -> Spec as JSON
    POST /run     {"code": str, "timeout": float, "inputs": {str: str}}
                  -> Result as JSON

and, for backends with ``spec.sessions`` (step-by-step proving):

    POST /start   {"code": str, "timeout": float}               -> Result
    POST /step    {"state": str, "step": str, "timeout": float} -> Result

where the Result carries ``details["state"]`` (a handle for further steps)
and ``details["goals"]``.

Writing a new backend means subclassing :class:`Adapter`, setting ``spec``
and implementing ``run``; :func:`sh` and :func:`workdir` cover the usual
"write files, run a binary with a timeout, parse stdout" shape.
"""

from __future__ import annotations

import importlib
import json
import os
import signal
import subprocess
import sys
import tempfile
import time
import traceback
from contextlib import contextmanager
from dataclasses import dataclass
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Iterator, Optional, Sequence, Union

from formalkit.core import Result, Spec, Verdict

MAX_TIMEOUT = float(os.environ.get("FORMALKIT_MAX_TIMEOUT", "600"))


class Adapter:
    """Translate between the formalkit protocol and one concrete tool."""

    spec: Spec

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        """Run ``code`` (plus any named ``inputs``) and return a Result.

        ``backend`` and ``elapsed`` are filled in by the server; adapters
        only decide the verdict, output and details.
        """
        raise NotImplementedError

    def start(self, code: str, timeout: float) -> Result:
        """Open a session at the single hole in ``code`` (sessions only).

        Return UNKNOWN with ``details["state"]`` and ``details["goals"]``, or
        ERROR when the code does not elaborate.
        """
        raise NotImplementedError

    def step(self, state: str, step: str, timeout: float) -> Result:
        """Apply one step to a session state (sessions only).

        Return UNKNOWN with a new ``state`` and its ``goals`` while goals
        remain, PROVED (with the assembled, independently checked proof in
        ``details["proof"]``) when none do, or ERROR when the step fails.
        States are immutable: the same state can be stepped many times.
        """
        raise NotImplementedError


@dataclass
class Proc:
    returncode: int
    stdout: str
    stderr: str
    timed_out: bool

    @property
    def out(self) -> str:
        """stdout and stderr together, the usual thing to show a model."""
        return (self.stdout + ("\n" + self.stderr if self.stderr.strip() else "")).strip()


def sh(
    cmd: Union[str, Sequence[str]],
    *,
    cwd: Union[str, Path, None] = None,
    timeout: float = 30,
    input: Optional[str] = None,
    env: Optional[dict] = None,
) -> Proc:
    """Run a command; on timeout kill its whole process group."""
    proc = subprocess.Popen(
        cmd,
        cwd=cwd,
        shell=isinstance(cmd, str),
        stdin=subprocess.PIPE if input is not None else subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        errors="replace",
        env={**os.environ, **(env or {})},
        start_new_session=True,
    )
    try:
        out, err = proc.communicate(input, timeout=timeout)
        return Proc(proc.returncode, out, err, False)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = proc.communicate()
        return Proc(-9, out or "", err or "", True)


@contextmanager
def workdir(files: Optional[dict] = None) -> Iterator[Path]:
    """A fresh temporary directory pre-populated with ``{name: text}`` files."""
    with tempfile.TemporaryDirectory(prefix="formalkit-") as d:
        path = Path(d)
        for name, text in (files or {}).items():
            (path / name).parent.mkdir(parents=True, exist_ok=True)
            (path / name).write_text(text, errors="replace")  # e.g. lone surrogates from JSON "\\ud800"
        yield path


def timed_out(proc: Proc, output: str = "") -> Result:
    """The standard Result for a run that hit its time limit."""
    return Result(Verdict.UNKNOWN, (output or proc.out + "\n").strip() + "\n[timeout]", {"timeout": True})


def load(name: str) -> Adapter:
    module = importlib.import_module(f"formalkit.adapters.{name.replace('-', '_')}")
    return module.ADAPTER


def execute(adapter: Adapter, code: str, timeout: float = 30, inputs: Optional[dict] = None) -> Result:
    """Run an adapter, never raising: crashes become ERROR results."""
    return _guarded(adapter, lambda t: adapter.run(code, timeout=t, **(inputs or {})), timeout)


def _guarded(adapter: Adapter, call, timeout: float) -> Result:
    timeout = max(1.0, min(float(timeout), MAX_TIMEOUT))
    start = time.monotonic()
    try:
        result = call(timeout)
    except NotImplementedError:
        raise
    except Exception:
        result = Result(Verdict.ERROR, f"internal adapter error:\n{traceback.format_exc()}")
    result.backend = adapter.spec.name
    result.elapsed = round(time.monotonic() - start, 3)
    return result


def _validate(req: object) -> dict:
    """Check a request body's shape; raise ValueError with a clear message."""
    if not isinstance(req, dict):
        raise ValueError("the request body must be a JSON object")
    for key in ("code", "state", "step"):
        if key in req and not isinstance(req[key], str):
            raise ValueError(f"{key!r} must be a string")
    timeout = req.get("timeout", 30)
    if isinstance(timeout, bool) or not isinstance(timeout, (int, float)) or timeout != timeout:
        raise ValueError("'timeout' must be a number of seconds")
    inputs = req.get("inputs") or {}
    if not isinstance(inputs, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in inputs.items()):
        raise ValueError("'inputs' must be an object mapping names to strings")
    return {**req, "timeout": timeout, "inputs": inputs}


def _text(req: dict, key: str) -> str:
    value = req.get(key, "")
    return value if isinstance(value, str) else str(value)


def make_server(adapter: Adapter, host: str = "0.0.0.0", port: int = 8080) -> ThreadingHTTPServer:
    """An HTTP server for ``adapter`` (port 0 picks a free port)."""

    class Handler(BaseHTTPRequestHandler):
        def _send(self, status: int, payload: dict) -> None:
            body = json.dumps(payload).encode()
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def do_GET(self) -> None:
            if self.path == "/health":
                self._send(200, {"ok": True, "backend": adapter.spec.name})
            elif self.path == "/spec":
                self._send(200, adapter.spec.to_dict())
            else:
                self._send(404, {"error": f"unknown path {self.path}"})

        def do_POST(self) -> None:
            routes = {
                "/run": lambda r, t: adapter.run(_text(r, "code"), timeout=t, **(r.get("inputs") or {})),
                "/start": lambda r, t: adapter.start(_text(r, "code"), timeout=t),
                "/step": lambda r, t: adapter.step(_text(r, "state"), _text(r, "step"), timeout=t),
            }
            if self.path not in routes:
                self._send(404, {"error": f"unknown path {self.path}"})
                return
            try:
                req = _validate(json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0)))))
            except Exception as e:
                self._send(400, {"error": f"bad request: {e}"})
                return
            try:
                result = _guarded(adapter, lambda t: routes[self.path](req, t), req["timeout"])
            except NotImplementedError:
                self._send(501, {"error": f"{adapter.spec.name} does not support {self.path}"})
                return
            except Exception as e:  # never drop a connection: clients read that as a dead backend
                self._send(500, {"error": f"internal error: {e}"})
                return
            self._send(200, result.to_dict())

        def log_message(self, fmt: str, *args) -> None:
            sys.stderr.write(f"[{adapter.spec.name}] {fmt % args}\n")

    return ThreadingHTTPServer((host, port), Handler)


def serve(adapter: Adapter, host: str = "0.0.0.0", port: int = 8080) -> None:
    server = make_server(adapter, host, port)
    print(f"formalkit backend '{adapter.spec.name}' listening on {host}:{port}", flush=True)
    server.serve_forever()


def main(argv: Optional[list] = None) -> None:
    argv = sys.argv[1:] if argv is None else argv
    if not argv:
        sys.exit("usage: python -m formalkit.server <backend> [port]")
    serve(load(argv[0]), port=int(argv[1]) if len(argv) > 1 else int(os.environ.get("PORT", 8080)))


if __name__ == "__main__":
    main()
