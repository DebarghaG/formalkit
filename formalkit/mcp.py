"""Serve formalkit backends as an MCP server over stdio.

    formalkit mcp z3 lean clingo

exposes each backend as one MCP tool, so any MCP client - Claude Code,
Claude Desktop, IDE agents - can call it. Register with Claude Code:

    claude mcp add formalkit -- formalkit mcp z3 lean clingo

Implements the small subset of MCP a tools-only server needs
(initialize, tools/list, tools/call, ping) with the stdlib.
"""

from __future__ import annotations

import json
import sys
from concurrent.futures import ThreadPoolExecutor
from typing import Any, Sequence

from formalkit import __version__
from formalkit.client import Backend, backend

PROTOCOL_VERSION = "2025-06-18"


def serve(backends: Sequence[str | Backend], timeout: float = 60) -> None:
    # Start every backend in the background: `initialize` must be answered at
    # once, even when containers are still starting (or images building).
    pool = ThreadPoolExecutor(max(1, len(backends)))
    pending = [pool.submit(lambda x=x: x if isinstance(x, Backend) else backend(x)) for x in backends]
    resolved: dict[str, Backend] = {}

    def ready() -> dict[str, Backend]:
        """The backends that started; failures are reported once on stderr and left out."""
        while pending:
            future = pending.pop(0)
            try:
                b = future.result()
                resolved[b.tool_name] = b
            except Exception as e:
                print(f"[formalkit mcp] a backend failed to start: {e}", file=sys.stderr, flush=True)
        return resolved

    def handle(method: str, params: dict[str, Any]) -> Any:
        if method == "initialize":
            return {
                "protocolVersion": params.get("protocolVersion", PROTOCOL_VERSION),
                "capabilities": {"tools": {}},
                "serverInfo": {"name": "formalkit", "version": __version__},
            }
        if method == "ping":
            return {}
        if method == "tools/list":
            return {"tools": [b.tool("mcp") for b in ready().values()]}
        if method == "tools/call":
            b = ready().get(params.get("name", ""))
            if b is None:
                return {"content": [{"type": "text", "text": f"unknown tool {params.get('name')!r}"}], "isError": True}
            result = b.call(params.get("arguments") or {}, timeout=timeout)
            return {
                "content": [{"type": "text", "text": result.feedback(limit=20000)}],
                "structuredContent": result.to_dict(),
                "isError": False,  # a failing proof is a result, not a tool failure
            }
        raise LookupError(method)

    def send(reply: dict[str, Any]) -> None:
        sys.stdout.write(json.dumps(reply) + "\n")
        sys.stdout.flush()

    for line in sys.stdin:
        if not line.strip():
            continue
        try:
            msg = json.loads(line)
        except ValueError:
            send({"jsonrpc": "2.0", "id": None, "error": {"code": -32700, "message": "parse error"}})
            continue
        if not isinstance(msg, dict):  # MCP does not use JSON-RPC batches
            send({"jsonrpc": "2.0", "id": None, "error": {"code": -32600, "message": "invalid request"}})
            continue
        if "id" not in msg:  # notification
            continue
        reply: dict[str, Any] = {"jsonrpc": "2.0", "id": msg["id"]}
        try:
            reply["result"] = handle(msg.get("method", ""), msg.get("params") or {})
        except LookupError:
            reply["error"] = {"code": -32601, "message": f"method not found: {msg.get('method')}"}
        except Exception as e:
            reply["error"] = {"code": -32603, "message": str(e)}
        send(reply)
