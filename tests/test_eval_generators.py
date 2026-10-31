"""Audit the evaluation suite's ground truth: generated problems must be right before models are scored on them."""

from __future__ import annotations

import itertools
import random
import re
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "evals"))
from scenarios import Bank, _holds, assignment_puzzle, banking_task, knapsack, statement  # noqa: E402

pytest.importorskip("openai")  # the scenarios module is importable without it, but evals/run.py needs it


def _parse_puzzle(q: str):
    people = re.match(r"(.*?) each own exactly one", q).group(1).replace(" and ", ", ").split(", ")
    things = re.search(r"all different: (.*?)\. ", q).group(1).split(", ")
    return people, things


def _clues_from_text(q: str):
    body = q.split("all different: ", 1)[1].split(". ", 1)[1].rsplit(". Who owns", 1)[0]
    clues = []
    for sentence in body.split(". "):
        if m := re.fullmatch(r"If (\w+) owns the (\w+), then (\w+) owns the (\w+)", sentence):
            clues.append(("if", (m[1], m[3]), (m[2], m[4])))
        elif m := re.fullmatch(r"(\w+) owns either the (\w+) or the (\w+)", sentence):
            clues.append(("either", m[1], (m[2], m[3])))
        elif m := re.fullmatch(r"(\w+) does not own the (\w+)", sentence):
            clues.append(("not", m[1], m[2]))
        elif m := re.fullmatch(r"(\w+) owns the (\w+)", sentence):
            clues.append(("is", m[1], m[2]))
        else:
            raise AssertionError(f"unparsed clue: {sentence!r}")
    return clues


@pytest.mark.parametrize("hard", [False, True])
def test_every_puzzle_has_exactly_one_solution_and_the_right_answer(hard):
    """Re-derive each puzzle from its English text alone and solve it independently."""
    rng = random.Random(11)
    for _ in range(15):
        p = assignment_puzzle(rng, size=rng.choice([6, 7] if hard else [4, 5]), hard=hard)
        people, things = _parse_puzzle(p["question"])
        clues = _clues_from_text(p["question"])
        if hard:
            assert all(kind != "is" for kind, *_ in clues)  # hard puzzles have only indirect clues
        sols = [dict(zip(people, perm)) for perm in itertools.permutations(things)
                if all(_holds(c, dict(zip(people, perm))) for c in clues)]  # fmt: skip
        assert len(sols) == 1
        target = re.search(r"Who owns the (\w+)\?", p["question"]).group(1)
        assert next(person for person, t in sols[0].items() if t == target) == p["answer"]


def test_puzzle_clues_are_true_of_the_unique_solution():
    rng = random.Random(3)
    from scenarios import _solutions

    people, things = ["A", "B", "C", "D"], ["w", "x", "y", "z"]
    truth = dict(zip(people, things))
    clues = [("not", "A", "x"), ("either", "B", ("x", "y")), ("if", ("C", "D"), ("y", "z"))]
    assert all(_holds(c, truth) for c in clues)
    assert truth in _solutions(people, things, clues)
    assert rng  # deterministic


@pytest.mark.parametrize("hard", [False, True])
def test_statement_truth_matches_an_independent_numeric_check(hard):
    rng = random.Random(7)
    seen = set()
    for _ in range(60):
        s = statement(rng, hard)
        seen.add(s["true"])
        prop = s["reference"].split(", ", 1)[1]
        check = prop.replace("∣", "|").replace("^", "**")
        for n in range(0, 40):
            expr = re.sub(r"\bn\b", str(n), check)
            if "Finset.range" in check:
                k, m = map(int, re.search(r"\((\d+) \* i \+ (\d+)\)", s["reference"]).groups())
                lhs = 2 * sum(k * i + m for i in range(n))
                rhs = eval(expr.split(" = ", 1)[1].replace(f"{n} - 1", f"max({n} - 1, 0)"))  # noqa: S307
                holds = lhs == rhs
            elif "|" in expr:
                d, prod = expr.split(" | ")
                holds = eval(prod) % int(d) == 0  # noqa: S307
            else:
                lhs, rhs = expr.split(" = ")
                holds = eval(lhs) == eval(rhs)  # noqa: S307
            if not holds:
                assert not s["true"], s
                break
        else:
            assert s["true"], s
    assert seen == {True, False}  # both kinds occur


def _dp_knapsack(items, cap):
    best = [0] * (cap + 1)
    for _, w, val in items:
        for c in range(cap, w - 1, -1):
            best[c] = max(best[c], best[c - w] + val)
    return best[cap]


def test_easy_knapsack_optimum_matches_dynamic_programming():
    rng = random.Random(5)
    for _ in range(20):
        p = knapsack(rng, 9)
        cap = int(re.search(r"at most (\d+) kg", p["question"]).group(1))
        items = [(m.group(1), int(m.group(2)), int(m.group(3)))
                 for m in re.finditer(r"([\w-]+): (\d+) kg, worth (\d+)", p["question"])]  # fmt: skip
        assert len(items) == 9 and p["answer"] == _dp_knapsack(items, cap)


def test_hard_knapsack_optimum_is_feasible_and_unbeatable():
    rng = random.Random(9)
    p = knapsack(rng, 12, hard=True)
    q = p["question"]
    cap, vol = map(int, re.search(r"at most (\d+) kg and (\d+) L", q).groups())
    items = [(m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)))
             for m in re.finditer(r"([\w-]+): (\d+) kg, (\d+) L, worth (\d+)", q)]  # fmt: skip
    names = [i[0] for i in items]
    needs = [(names.index(a), names.index(b)) for a, b in re.findall(r"Taking ([\w-]+) requires also taking ([\w-]+)\.", q)]
    conflicts = [(names.index(a), names.index(b)) for a, b in re.findall(r"([\w-]+) and ([\w-]+) cannot both be taken", q)]
    best = 0
    for mask in itertools.product([0, 1], repeat=len(items)):
        if sum(i[1] for i, m in zip(items, mask) if m) > cap or sum(i[2] for i, m in zip(items, mask) if m) > vol:
            continue
        if any(mask[a] and not mask[b] for a, b in needs) or any(mask[a] and mask[b] for a, b in conflicts):
            continue
        best = max(best, sum(i[3] for i, m in zip(items, mask) if m))
    assert needs and conflicts and best == p["answer"]


def test_banking_tasks_are_balanced_and_the_oracle_is_consistent():
    rng = random.Random(1)
    tasks = [banking_task(rng) for _ in range(400)]
    allowed = [Bank(t["balance"], t["verified"]).allowed(t["to"], t["amount"]) for t in tasks]
    assert 0.4 < sum(allowed) / len(tasks) < 0.6
    for t, ok in zip(tasks, allowed):
        expected = 0 < t["amount"] <= t["balance"] and (t["amount"] <= 1000 or t["verified"]) and t["to"] != "acct-9931"
        assert ok == expected
