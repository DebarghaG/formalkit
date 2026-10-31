"""The solver in control, the model as a subroutine at specific decision points.

The model supplies local judgments - plausibilities, quantifier instances,
search neighborhoods - and the symbolic engine integrates them and keeps
the final say. Each pattern is sound by construction: nothing the model
says reaches the final verdict without being checked or being a mere hint.
"""

from __future__ import annotations

import json
import random
import re
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from typing import Any, Callable, Sequence

from formalkit.client import Backend
from formalkit.core import Result, Verdict
from formalkit.evidence import top_level_forms
from formalkit.llm import LLM, extract_code

# -- OrLog: the model scores atoms, ProbLog does the logic -----------------------------------

_SOFT = re.compile(r"^(\s*)\?\s*::\s*(.+?)\.\s*$", re.M)
_VARIABLE = re.compile(r"(?<![\w])[A-Z_]\w*")


def _strip_quoted(atom: str) -> str:
    return re.sub(r"'[^']*'|\"[^\"]*\"", "''", atom)


@dataclass
class Scored:
    result: Result
    scores: dict[str, float]  # the probability the model gave each soft atom


def soft_facts(llm: LLM, problog: Backend, program: str, *, context: str = "", timeout: float = 60) -> Scored:
    """Fill ``?::atom.`` facts with the model's plausibilities, then let ProbLog combine them (OrLog).

    The model only judges atomic statements; conjunction, disjunction,
    negation and rules are computed exactly by ProbLog.
    """
    atoms = list(dict.fromkeys(m.group(2).strip() for m in _SOFT.finditer(program)))
    if not atoms:
        return Scored(problog.run(program, timeout=timeout), {})
    open_atoms = [a for a in atoms if ":-" in a or _VARIABLE.search(_strip_quoted(a))]
    if open_atoms:  # a plausibility is a judgment about one concrete statement
        return Scored(Result(Verdict.ERROR, "soft facts must be ground atoms (no variables, no rules): "
                             + ", ".join(open_atoms), backend=problog.name), {})  # fmt: skip
    reply = llm.ask(
        "Estimate, for each statement, the probability (0 to 1) that it is true."
        + (f"\n\nWhat is known:\n{context}" if context else "")
        + "\n\nStatements:\n" + "\n".join(f"- {a}" for a in atoms)
        + '\n\nReply with a JSON object mapping each statement exactly as written to its probability.'
    )[0]  # fmt: skip
    try:
        raw = json.loads(extract_code(reply))
    except ValueError:  # almost-JSON (trailing commas, comments): take the "atom": number pairs
        raw = {k: float(v) for k, v in re.findall(r'"([^"]+)"\s*:\s*(-?\d+(?:\.\d+)?(?:[eE]-?\d+)?)', reply)}
    by_shape = {re.sub(r"\s+", "", str(k)): v for k, v in raw.items()} if isinstance(raw, dict) else {}
    scores = {a: _probability(raw.get(a, by_shape.get(re.sub(r"\s+", "", a)))) if isinstance(raw, dict) else 0.5
              for a in atoms}  # fmt: skip
    filled = _SOFT.sub(lambda m: f"{m.group(1)}{scores[m.group(2).strip()]}::{m.group(2).strip()}.", program)
    return Scored(problog.run(filled, timeout=timeout), scores)


def _probability(value: Any) -> float:
    try:
        return min(1.0, max(0.0, float(value)))
    except (TypeError, ValueError):
        return 0.5  # no judgment: maximally uncertain


# -- AquaForte: the model proposes quantifier instances, the solver validates them ----------


@dataclass
class Instantiated:
    result: Result
    accepted: list[str] = field(default_factory=list)  # instances proven to follow from the axioms
    rejected: list[str] = field(default_factory=list)


def instantiate(
    llm: LLM,
    smt: Backend,
    script: str,
    *,
    rounds: int = 2,
    timeout: float = 30,
    check_timeout: float = 5,
) -> Instantiated:
    """Help an SMT solver with quantifiers by proposing ground instances (AquaForte).

    When the solver answers ``unknown``, the model proposes instances of the
    universally quantified assertions. Each is added only after the solver
    proves it follows from those assertions (``axioms ∧ ¬instance`` is
    unsat), so adding it never changes the answer - it can only help the
    solver find it. Rejected proposals are fed back.
    """
    out = Instantiated(smt.run(script, timeout=timeout))
    forms = [script[a:b] for a, b in top_level_forms(script)]
    # The validation query is a separate, small problem: it keeps the declarations but not the
    # script's solver options, which may be exactly what crippled the solver (e.g. no MBQI).
    decls = [f for f in forms if _head(f) in ("set-logic", "declare-sort", "define-sort", "declare-fun", "declare-const",
                                               "define-fun", "define-fun-rec", "define-funs-rec", "declare-datatypes",
                                               "declare-datatype")]
    axioms = [f for f in forms if _head(f) == "assert" and re.search(r"\(\s*forall\b", f)]  # fmt: skip
    for _ in range(rounds):
        if out.result.verdict is not Verdict.UNKNOWN or not axioms:
            break  # decided, or rejected (error): instances cannot help
        reply = llm.ask(
            f"The SMT solver answered `{out.result.verdict}` on this script:\n\n```\n{script}\n```\n\n"
            "Propose ground instances of its universally quantified assertions that would help decide it: "
            "substitute concrete terms for the bound variables. One `(assert ...)` per instance, all in a "
            "single fenced code block."
            + ("\n\nThese earlier proposals could not be shown to follow from the axioms; avoid them:\n"
               + "\n".join(out.rejected)
               if out.rejected else "")
        )[0]  # fmt: skip
        code = extract_code(reply)
        proposals = [f for f in dict.fromkeys(code[a:b] for a, b in top_level_forms(code))
                     if _head(f) == "assert" and f not in out.accepted and f not in out.rejected]  # fmt: skip

        def follows(instance: str) -> bool:
            body = instance.strip()[len("(assert") : -1].strip()
            check = "\n".join([*decls, *axioms, f"(assert (not {body}))", "(check-sat)"])
            return smt.run(check, timeout=check_timeout).verdict is Verdict.UNSAT

        with ThreadPoolExecutor(8) as pool:  # validations are independent
            for instance, ok in zip(proposals, pool.map(follows, proposals)):
                (out.accepted if ok else out.rejected).append(instance)
        if out.accepted:
            out.result = smt.run(_insert_before_check(script, out.accepted), timeout=timeout)
            out.result.details["instances"] = list(out.accepted)
    return out


def _head(form: str) -> str:
    match = re.match(r"\(\s*([^\s()]+)", form)
    return match.group(1) if match else ""


def _insert_before_check(script: str, asserts: Sequence[str]) -> str:
    match = re.search(r"\(\s*check-sat\b", script)
    at = match.start() if match else len(script)
    return script[:at] + "\n".join(asserts) + "\n" + script[at:]


# -- LLM-LNS: the model chooses the neighborhood, the solver searches it ---------------------


@dataclass
class Neighborhoods:
    result: Result  # the best solution found (sat; optimal only if the first full solve proved it)
    objective: float | None
    history: list[tuple[list[str], float | None]] = field(default_factory=list)  # (freed units, objective)
    empty: int = 0  # rounds whose proposal named nothing freeable (no solve was run)


def lns(
    propose: Callable[[dict[str, Any], list], Sequence[str]],
    minizinc: Backend,
    model: str,
    *,
    rounds: int = 5,
    timeout: float = 30,
    **inputs: str,
) -> Neighborhoods:
    """Large-neighborhood search with a model-chosen neighborhood (LLM-LNS).

    Solve once; then, each round, ``propose(incumbent, history)`` names what
    to *free* - scalar variables, whole 1-D arrays (``take``) or single
    elements (``take[3]``, in the model's own index set) - every other unit
    is fixed to its incumbent value, and MiniZinc re-optimizes inside that
    neighborhood. Improvements are kept. Anything the model forgets stays
    fixed, so every result is a genuine solution of the original model.
    Values that cannot be fixed (2-D arrays, sets, enums) stay free.
    """
    sense = "min" if re.search(r"\bsolve\s+minimize\b", model) else "max" if re.search(r"\bsolve\s+maximize\b", model) else None
    best = minizinc.run(model, timeout=timeout, **inputs)
    out = Neighborhoods(best, _objective(best))
    if sense is None or best.verdict not in (Verdict.SAT, Verdict.OPTIMAL) or best.verdict is Verdict.OPTIMAL:
        return out
    for _ in range(rounds):
        incumbent = {k: v for k, v in (out.result.model or {}).items() if not k.startswith("_")}
        units = freeable(incumbent, model)
        free = _resolve(propose(incumbent, out.history), units, incumbent)
        if not free:  # nothing to re-optimize: solving the fully fixed model would only repeat the incumbent
            out.empty += 1
            out.history.append(([], None))
            continue
        fixes = [f"constraint {unit} = {_mzn(value)};" for unit, value in units.items() if unit not in free]
        result = minizinc.run(model + "\n" + "\n".join(fixes) + "\n", timeout=timeout, **inputs)
        value = _objective(result)
        out.history.append((sorted(free), value))
        if value is not None and out.objective is not None and (value < out.objective if sense == "min" else value > out.objective):
            result.verdict = Verdict.SAT  # optimal within a neighborhood is not optimal overall
            out.result, out.objective = result, value
    return out


def freeable(incumbent: dict[str, Any], model: str) -> dict[str, Any]:
    """Every unit LNS can fix or free, with its incumbent value: scalars by name, 1-D array elements as
    ``name[i]`` in the array's MiniZinc index set (JSON output drops it; it is read from the model)."""
    units: dict[str, Any] = {}
    for name, value in incumbent.items():
        if isinstance(value, list):
            if value and all(_mzn(v) is not None and not isinstance(v, list) for v in value):
                base = _index_base(model, name)
                units.update({f"{name}[{base + i}]": v for i, v in enumerate(value)})
        elif _mzn(value) is not None:
            units[name] = value
    return units


def _index_base(model: str, name: str) -> int:
    """The first index of 1-D array ``name``: ``array[1..n]`` -> 1, ``array[0..9]`` -> 0, or via a named set."""
    decl = re.search(rf"array\s*\[\s*([^\]]+?)\s*\]\s*of\s+var\b[^;:]*:\s*{re.escape(name)}\b", model)
    if decl:
        index = decl.group(1)
        literal = re.match(r"(-?\d+)\s*\.\.", index)
        if literal:
            return int(literal.group(1))
        named = re.search(rf"\b{re.escape(index)}\s*=\s*(-?\d+)\s*\.\.", model)
        if named:
            return int(named.group(1))
    return 1  # MiniZinc's usual convention


def _resolve(names: Sequence[str], units: dict[str, Any], incumbent: dict[str, Any]) -> set[str]:
    """Proposed names -> freeable units: ``take[3]`` is one element, ``take`` the whole array."""
    free: set[str] = set()
    for raw in names:
        if not isinstance(raw, str):
            continue
        name = re.sub(r"\s+", "", raw)
        if name in units:
            free.add(name)
        elif name in incumbent:
            free.update(u for u in units if u == name or u.startswith(name + "["))
    return free


def _objective(result: Result) -> float | None:
    value = result.details.get("objective")
    return float(value) if isinstance(value, (int, float)) else None


def _mzn(value: Any) -> str | None:
    """A MiniZinc literal for a JSON value: scalars and 1-d arrays of scalars (else None: leave it free)."""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return repr(value)
    if isinstance(value, list) and all(isinstance(v, (int, float)) and not isinstance(v, bool) for v in value):
        return "[" + ", ".join(repr(v) for v in value) + "]"
    return None


def llm_neighborhood(llm: LLM, model: str, k: int = 3, *, fallback: bool = True) -> Callable[[dict[str, Any], list], list[str]]:
    """A ``propose`` for :func:`lns`: the model picks up to ``k`` units to re-optimize.

    Units are scalar variables and single array elements (``take[3]``); naming
    a whole array frees all of it. When the reply names nothing freeable (e.g.
    a reasoning model ran out of tokens), ``fallback`` picks ``k`` units at
    random - the classic LNS move - so a bad reply costs one round, not the
    search. For reasoning models, ``LLM(..., reasoning_effort="low")`` keeps
    these calls fast.
    """

    def propose(incumbent: dict[str, Any], history: list) -> list[str]:
        units = freeable(incumbent, model)
        tried = "\n".join(f"- freed {names}: objective {value}" for names, value in history) or "(none yet)"
        reply = llm.ask(
            f"MiniZinc model:\n```\n{model}\n```\n\nCurrent solution: {json.dumps(incumbent)}\n\n"
            f"Neighborhoods tried so far:\n{tried}\n\nWhich up to {k} variables or array elements (written like "
            f"x or take[3], using the model's own indices) should be re-optimized next, keeping all others fixed, "
            'to most likely improve the objective? Think briefly. Reply with only a JSON list of names, e.g. ["x", "take[3]"].'
        )[0]
        try:
            names = json.loads(extract_code(reply))
        except ValueError:
            names = re.findall(r"[A-Za-z_]\w*(?:\s*\[\s*-?\d+\s*\])?", reply)
        names = [n for n in (names if isinstance(names, list) else []) if isinstance(n, str)][:k]
        chosen = sorted(_resolve(names, units, incumbent))  # a whole array may stand for many units
        if not chosen and fallback and units:
            chosen = random.Random(len(history)).sample(sorted(units), min(k, len(units)))
        return chosen

    return propose
