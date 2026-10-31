from __future__ import annotations

import json
import os
import re

from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

AG = os.environ.get("ALPHAGEOMETRY", "/opt/alphageometry")

# Runs inside AlphaGeometry's own module namespace; prints one JSON line.
_RUNNER = r'''
import json, os, sys, traceback
sys.path.insert(0, os.environ["ALPHAGEOMETRY"])
os.chdir(os.environ["ALPHAGEOMETRY"])
from absl import logging
logging.set_verbosity(logging.FATAL)
import ddar, graph as gh, numericals as nm, pretty as pt, problem as pr

def emit(**kw):
    print("@@RESULT@@" + json.dumps(kw)); sys.exit(0)

BACK = {}  # AlphaGeometry renames points internally; map them back to the user's names

def nl(dep):
    names = [BACK.get(a.name, a.name).upper() for a in dep.args]
    return pt.pretty_nl(dep.name, [(n[0] + "_" + n[1:]) if len(n) > 1 else n for n in names])

# Constructions with free choices (a point on a line, which intersection) give
# diagrams where a true goal can fail; AlphaGeometry resamples until it holds.
# Sample up to DIAGRAMS diagrams within ~30% of the time budget: "refuted"
# means the goal failed in every one of them.
DIAGRAMS = 40
import time as _time
SAMPLE_UNTIL = _time.monotonic() + 0.3 * float(sys.argv[2])
text = open(sys.argv[1]).read()
defs = pr.Definition.from_txt_file("defs.txt", to_dict=True)
rules = pr.Theorem.from_txt_file("rules.txt", to_dict=True)
try:
    p = pr.Problem.from_txt(text.strip())
except KeyError as e:
    emit(status="error", message=f"cannot parse problem: undefined point or construction {e}")
except Exception as e:
    emit(status="error", message=f"cannot parse problem: {type(e).__name__}: {e}")
if p.goal is None:
    emit(status="error", message="no goal: write the problem as '<constructions> ? <goal predicate>'")
try:
    orig = pr.Problem.from_txt(text.strip(), translate=False)
    for c0, c1 in zip(orig.clauses, p.clauses):
        BACK.update(zip(c1.points, c0.points))
except Exception:
    pass
for clause in pr.Problem.from_txt(text.strip(), translate=False).clauses:
    for c in clause.constructions:
        if c.name not in defs:
            emit(status="error", message=f"unknown construction {c.name!r} (see AlphaGeometry's defs.txt)")
        want = defs[c.name].construction.args
        # The clause's new points may be left implicit: `a1 = on_line b c`, `a b c = triangle`.
        implicit = len(c.args) + len(clause.points) == len(want) and not set(c.args) & set(clause.points)
        if len(c.args) != len(want) and not implicit:
            emit(status="error", message=f"{c.name} takes {len(want)} points ({c.name} {' '.join(want)}), "
                                         f"got {len(c.args)}: {c.name} {' '.join(c.args)}")
goal = p.goal
goal_text = text.split("?", 1)[1].strip()  # translate() renames points

# Graph.build_problem resamples random diagrams until the goal holds
# numerically - forever, for a false goal. Build without the goal and do the
# numerical check ourselves, over a bounded number of random diagrams.
p.goal = None
holds = False
tried = 0
for attempt in range(DIAGRAMS):
    if attempt >= 5 and _time.monotonic() > SAMPLE_UNTIL:
        break
    tried += 1
    try:
        g, _ = gh.Graph.build_problem(p, defs, verbose=False)
        args = [g.get(x, lambda: int(x)) for x in goal.args]
        holds = bool(nm.check(goal.name, args))
    except KeyError as e:
        emit(status="error", message=f"unknown construction or point name: {e}")
    except Exception as e:
        emit(status="error", message=f"{type(e).__name__}: {e}", trace=traceback.format_exc(limit=3))
    if holds:
        break
p.goal = goal
if not holds and "@" in text:
    # Fixed coordinates (x@1.0_2.0) pick a configuration our random diagrams need not reproduce.
    emit(status="inconclusive", goal=goal_text,
         message=f"the goal failed numerically in {tried} diagrams, but the problem fixes point coordinates "
                 "(x@...), which choose a configuration these diagrams may not reproduce: no refutation claimed")
if not holds:
    try:  # coordinates of one diagram where the goal fails, under the user's point names
        coords = {BACK.get(q.name, q.name): [round(float(q.num.x), 4), round(float(q.num.y), 4)]
                  for q in g.all_points()}
    except Exception:
        coords = None
    emit(status="refuted", goal=goal_text, counterexample=coords,
         message=f"the goal is false in all {tried} randomly constructed diagrams")

goal_args = g.names2nodes(goal.args)
ddar.solve(g, rules, p, max_level=1000, timeout=int(sys.argv[2]))
if not g.check(goal.name, goal_args):
    emit(status="saturated", goal=goal_text)

setup, aux, steps, refs = ddar.get_proof_steps(g, p.goal, merge_trivials=False)
premises = []
for prem, _ in setup:
    premises += [f"{nl(x)} [{refs[x.hashed()]:02}]" for x in prem]
lines = []
for i, (prem, [con]) in enumerate(steps):
    lhs = " & ".join(f"{nl(x)} [{refs[x.hashed()]:02}]" for x in prem) or "similarly"
    refs[con.hashed()] = len(refs)
    rhs = nl(con) + ("" if i == len(steps) - 1 else f" [{refs[con.hashed()]:02}]")
    rule = f"  ({con.rule_name})" if con.rule_name else ""
    lines.append(f"{i + 1:03}. {lhs} => {rhs}{rule}")
emit(status="proved", goal=goal_text, premises=premises, steps=lines)
'''


# Goal predicates DD+AR can check, with their number of point arguments.
GOALS = {"coll": 3, "midp": 3, "cyclic": 4, "perp": 4, "para": 4, "cong": 4, "circle": 4, "eqangle": 8,
         "eqratio": 8, "eqangle6": 6, "eqratio6": 6, "simtri": 6, "simtri2": 6, "contri": 6, "contri2": 6}  # fmt: skip


def _normalize(code: str) -> str:
    """One line, single spaces, canonical `; ` and ` ? ` separators; `#` comment lines dropped."""
    text = " ".join(l.strip() for l in code.splitlines() if l.strip() and not l.strip().startswith("#"))
    text = re.sub(r"\s+", " ", text)
    text = re.sub(r"\s*;\s*", "; ", text).strip("; ")
    return re.sub(r"\s*\?\s*", " ? ", text).strip()


def _check(problem: str) -> str | None:
    """A message for problems DD+AR would misread, else None."""
    if not problem:
        return "empty problem: write '<constructions> ? <goal>'"
    if problem.endswith("?"):
        return "empty goal after '?': write e.g. '? perp a b c d'"
    constructions, _, goal = problem.partition(" ? ")
    defined: set = set()
    for clause in filter(None, (c.strip() for c in constructions.split(";"))):
        if "=" not in clause:
            return f"clause {clause!r} must look like 'x y = construction args'"
        points = [q.split("@", 1)[0] for q in clause.split("=", 1)[0].split()]  # `x@1.0_2.0`: fixed coordinates
        again = [q for q in points if q in defined]
        if again:
            return f"point {again[0]!r} is defined twice; each clause must introduce new points ({clause!r})"
        defined.update(points)
    if goal:
        name, *args = goal.split()
        if name not in GOALS:
            return f"unknown goal predicate {name!r}; use one of: {', '.join(GOALS)}"
        if len(args) != GOALS[name]:
            return f"goal {name} takes {GOALS[name]} points, got {len(args)}: {goal!r}"
        undefined = [q for q in args if q not in defined]
        if undefined:
            return f"goal uses undefined point(s): {', '.join(undefined)}"
    return None


class DDAR(Adapter):
    spec = Spec(
        name="ddar",
        family="geometry engine",
        language="AlphaGeometry problem language",
        emits="a plane-geometry construction (points built by named constructions) and a goal predicate.",
        authority="DD+AR: deductive database rules plus algebraic (angle/ratio/distance) chasing, AlphaGeometry's symbolic engine.",
        feedback="a numbered synthetic proof, or saturation without the goal, or a numerical counterexample.",
        use="olympiad-style Euclidean geometry, where general logics lose the useful structure.",
        guidance=(
            "Write one problem: `<constructions> ? <goal>`. Constructions are `;`-separated "
            "`x = construction args` clauses (from AlphaGeometry's defs.txt), e.g. `a b c = triangle a b c`, "
            "`d = midpoint d a b`, `h = on_tline h b a c, on_tline h c a b`, `o = circle o a b c`, "
            "`e = on_line e a c, on_line e b d`, `f = foot f a b c`. Goals: coll, cyclic, perp, para, cong, "
            "eqangle, eqratio, midp, simtri, contri with point arguments, e.g. `? perp a h b c`. "
            "proved = DD+AR derived the goal (the proof is returned); refuted = the goal is false in every one of up to 40 "
            "randomly sampled diagrams (numerical evidence, not a proof); unknown = deduction saturated without reaching the goal - DD+AR is "
            "incomplete, so try adding an auxiliary point construction and run again; error = unknown "
            "construction, wrong arity, or degenerate construction."
        ),
        example="a b c = triangle a b c; d = on_tline d b a c, on_tline d c a b; e = on_line e a c, on_line e b d ? perp a d b c",
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        problem = _normalize(code)
        problem_error = _check(problem)
        if problem_error:
            return Result(Verdict.ERROR, problem_error, {"message": problem_error})
        with workdir({"runner.py": _RUNNER, "problem.txt": problem}) as d:
            proc = sh(["python3", str(d / "runner.py"), str(d / "problem.txt"), str(max(1, int(timeout) - 2))],
                      timeout=timeout, env={"ALPHAGEOMETRY": AG})  # fmt: skip
        if proc.timed_out:
            return timed_out(proc, "DD+AR timed out before saturating")
        marker = [l for l in proc.stdout.splitlines() if l.startswith("@@RESULT@@")]
        if not marker:
            return Result(Verdict.ERROR, proc.out[-3000:] or "DD+AR crashed", {})
        r = json.loads(marker[-1][len("@@RESULT@@"):])
        status = r.pop("status")
        if status == "proved":
            body = " * premises:\n" + "\n".join(r["premises"]) + "\n * proof:\n" + "\n".join(r["steps"])
            return Result(Verdict.PROVED, f"goal {r['goal']} proved\n{body}", {"goal": r["goal"], "proof": body})
        if status == "refuted":
            coords = r.get("counterexample")
            shown = "".join(f"\n  {k} = ({x}, {y})" for k, (x, y) in (coords or {}).items())
            text = f"goal {r['goal']}: {r['message']}" + (f"\none such diagram:{shown}" if shown else "")
            return Result(Verdict.REFUTED, text, {"goal": r["goal"], "counterexample": coords or r["message"]})
        if status == "inconclusive":
            return Result(Verdict.UNKNOWN, f"goal {r['goal']}: {r['message']}", {"goal": r["goal"], "goals": [r["goal"]]})
        if status == "saturated":
            return Result(Verdict.UNKNOWN, f"DD+AR saturated without proving {r['goal']}; "
                          "try adding an auxiliary construction", {"goal": r["goal"], "goals": [r["goal"]]})  # fmt: skip
        message = r.get("message", "")
        if "Argument mismatch" in message:
            message = f"wrong number of arguments in a construction: {message.split('Argument mismatch.', 1)[-1].strip()}"
        return Result(Verdict.ERROR, message, r)  # the runner's traceback stays in details


ADAPTER = DDAR()
