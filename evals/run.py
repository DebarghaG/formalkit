"""Run the user-scenario evaluations against a real model and the real tools.

    OPENAI_BASE_URL=https://api.deepseek.com OPENAI_API_KEY=... \\
        python evals/run.py [researcher data_builder practitioner agent_builder] --n 8 --k 3 --model deepseek-flash

Prints a per-stage report for each scenario and writes everything (every
attempt, every stage) to evals/results/<timestamp>.json.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

from openai import OpenAI

sys.path.insert(0, str(Path(__file__).resolve().parent))
import formalkit  # noqa: E402
from scenarios import SCENARIOS  # noqa: E402


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("scenarios", nargs="*", default=list(SCENARIOS))
    p.add_argument("--n", type=int, default=8, help="problems per scenario")
    p.add_argument("--k", type=int, default=3, help="independent runs per problem")
    p.add_argument("--seed", type=int, default=int(time.time()) % 10_000)
    p.add_argument("--model", default="deepseek-flash")
    p.add_argument("--hard", action="store_true", help="harder problems: bigger, indirect, multi-constraint")
    args = p.parse_args()

    llm = formalkit.LLM(OpenAI(), args.model, max_tokens=8192)
    out = {"model": args.model, "n": args.n, "k": args.k, "seed": args.seed, "hard": args.hard, "scenarios": {}}
    for name in args.scenarios:
        start = time.time()
        scenario = SCENARIOS[name](llm, args.n, args.k, args.seed, hard=args.hard)
        print(f"\n=== {scenario.name}: {scenario.user}  ({time.time() - start:.0f}s)", flush=True)
        for label, report in scenario.reports.items():
            print(report.summary(label))
        for note in scenario.notes:
            print(f"  * {note}")
        out["scenarios"][name] = {
            "user": scenario.user,
            "notes": scenario.notes,
            "reports": {label: {"rates": r.rates(), "rows": r.rows} for label, r in scenario.reports.items()},
        }
    results = Path(__file__).resolve().parent / "results"
    results.mkdir(exist_ok=True)
    path = results / f"{time.strftime('%Y%m%d-%H%M%S')}-{args.model}{'-hard' if args.hard else ''}.json"
    path.write_text(json.dumps(out, indent=1, default=str))
    print(f"\nLLM usage: {llm.usage}\nwrote {path}")


if __name__ == "__main__":
    main()
