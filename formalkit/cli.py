"""Command line: formalkit list | build | up | down | spec | run | mcp | solve."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from formalkit import docker
from formalkit.client import backend
from formalkit.registry import BACKENDS, FAMILIES, VIRTUAL, entry


def _names(names: list[str], all_: bool) -> list[str]:
    if all_:
        return list(BACKENDS)
    if not names:
        sys.exit("name at least one backend (or pass --all)")
    return names


def cmd_list(args: argparse.Namespace) -> None:
    running = set(docker.running())
    for family in FAMILIES:
        print(family)
        for e in BACKENDS.values():
            if e.family == family:
                state = "running" if e.name in running else ("built" if docker.has_image(e.name) else "-")
                print(f"  {e.name:<10} {state:<8} {e.summary}")
        for v in VIRTUAL.values():
            if v.family == family:
                print(f"  {v.name:<10} {'virtual':<8} {v.summary}")


def cmd_build(args: argparse.Namespace) -> None:
    images = {}  # one build per image; several backends may share one
    for n in _names(args.names, args.all):
        images.setdefault(entry(n).image, n)
    failed = []
    for name in images.values():
        print(f"== building {docker.image(name)}", flush=True)
        try:
            docker.build(name, pull=args.pull)
        except docker.DockerError as e:  # keep building the others; report at the end
            failed.append(name)
            print(f"   FAILED: {str(e).splitlines()[0]}", file=sys.stderr, flush=True)
            continue
        # Running containers keep serving the old image: replace them (next use starts the new one).
        for other, e in BACKENDS.items():
            if e.image == BACKENDS[name].image and docker.url(other):
                docker.down(other)
                print(f"   stopped running {other} so the next use runs the new image", flush=True)
    if failed:
        sys.exit(f"error: failed to build {', '.join(docker.image(n) for n in failed)} (existing images, if any, are unchanged)")


def cmd_up(args: argparse.Namespace) -> None:
    for name in _names(args.names, args.all):
        if name in VIRTUAL:
            backend(name)  # starts the backends it is built from
            print(f"{name}\tvirtual", flush=True)
        else:
            print(f"{name}\t{docker.up(name)}", flush=True)


def cmd_down(args: argparse.Namespace) -> None:
    for name in _names(args.names, False) if not args.all else docker.running():
        docker.down(name)
        print(f"stopped {name}")


def cmd_spec(args: argparse.Namespace) -> None:
    b = backend(args.name, url=args.url)
    print(json.dumps(b.spec.to_dict(), indent=2) if args.json else b.spec.describe())


def cmd_run(args: argparse.Namespace) -> None:
    b = backend(args.name, url=args.url)  # fail fast on an unknown backend, before reading any input
    code = sys.stdin.read() if args.file == "-" else Path(args.file).read_text()
    inputs = {}
    for item in args.input:
        key, _, path = item.partition("=")
        inputs[key] = Path(path).read_text()
    result = b.run(code, timeout=args.timeout, **inputs)
    if args.json:
        print(json.dumps(result.to_dict(), indent=2))
    else:
        print(result.verdict.value)
        if result.output.strip():
            print(result.output.rstrip())
    sys.exit(0 if result.decisive else 1)


def cmd_mcp(args: argparse.Namespace) -> None:
    from formalkit.mcp import serve

    serve(_names(args.names, args.all), timeout=args.timeout)


def cmd_solve(args: argparse.Namespace) -> None:
    try:
        from openai import OpenAI
    except ImportError:
        sys.exit("`formalkit solve` needs the openai package: pip install 'formalkit[agent]'")
    from formalkit.agent import Agent

    client = OpenAI(base_url=args.base_url) if args.base_url else OpenAI()
    agent = Agent(client, args.model, args.backends.split(","), max_iterations=args.max_iterations, timeout=args.timeout)
    answer = agent.solve(args.question)
    if args.json:
        print(json.dumps(answer.to_dict(), indent=2))
        return
    for step in answer.steps:
        print(f"--- {step.backend}: {step.result.verdict}", file=sys.stderr)
    print(answer)


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(prog="formalkit", description="One interface between LLMs and formal tools.")
    sub = p.add_subparsers(dest="cmd", required=True)

    sub.add_parser("list", help="list backends and their state").set_defaults(fn=cmd_list)

    for name, fn, helptext in [
        ("build", cmd_build, "build backend images"),
        ("up", cmd_up, "start backend containers"),
    ]:
        s = sub.add_parser(name, help=helptext)
        s.add_argument("names", nargs="*")
        s.add_argument("--all", action="store_true")
        if name == "build":
            s.add_argument("--pull", action="store_true", help="pull newer base images")
        s.set_defaults(fn=fn)

    s = sub.add_parser("down", help="stop backend containers")
    s.add_argument("names", nargs="*")
    s.add_argument("--all", action="store_true", help="stop every running formalkit backend")
    s.set_defaults(fn=cmd_down)

    s = sub.add_parser("spec", help="show what a backend accepts and returns")
    s.add_argument("name")
    s.add_argument("--url")
    s.add_argument("--json", action="store_true")
    s.set_defaults(fn=cmd_spec)

    s = sub.add_parser("run", help="run a file through a backend")
    s.add_argument("name")
    s.add_argument("file", help="input file, or - for stdin")
    s.add_argument("-i", "--input", action="append", default=[], metavar="KEY=FILE", help="extra named input")
    s.add_argument("-t", "--timeout", type=float, default=30)
    s.add_argument("--url")
    s.add_argument("--json", action="store_true")
    s.set_defaults(fn=cmd_run)

    s = sub.add_parser("mcp", help="serve backends as an MCP server on stdio")
    s.add_argument("names", nargs="*")
    s.add_argument("--all", action="store_true")
    s.add_argument("-t", "--timeout", type=float, default=60)
    s.set_defaults(fn=cmd_mcp)

    s = sub.add_parser("solve", help="answer a question with an LLM + backends")
    s.add_argument("question")
    s.add_argument("-b", "--backends", default="z3")
    s.add_argument("-m", "--model", default="gpt-5")
    s.add_argument("--base-url", help="OpenAI-compatible endpoint (vLLM, sglang, ...)")
    s.add_argument("--max-iterations", type=int, default=10)
    s.add_argument("-t", "--timeout", type=float, default=30)
    s.add_argument("--json", action="store_true")
    s.set_defaults(fn=cmd_solve)

    args = p.parse_args(argv)
    try:
        args.fn(args)
    except docker.DockerError as e:
        sys.exit(f"error: {e}")
    except KeyError as e:  # unknown backend
        sys.exit(f"error: {e.args[0]}")
    except OSError as e:  # unreadable input file
        sys.exit(f"error: {e.strerror}: {e.filename}" if e.filename else f"error: {e}")


if __name__ == "__main__":
    main()
