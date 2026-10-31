from __future__ import annotations

import os
import re
import time

from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

FD = ["python3", "/opt/downward/fast-downward.py"]
ALIASES = {"satisficing": "lama-first", "optimal": "seq-opt-lmcut"}

# Fast Downward driver exit codes (driver/returncodes.py).
_PLAN_FOUND = {0, 1, 2, 3}
_UNSOLVABLE = {10, 11}
_LIMITS = {12, 20, 21, 22, 23, 24}
_UNSUPPORTED = {34, 37}


def _tail(text: str, n: int = 40) -> str:
    lines = text.strip().splitlines()
    return "\n".join(lines[-n:])


PLANNER_MEMORY = os.environ.get("DOWNWARD_MEMORY", "4G")


class Downward(Adapter):
    spec = Spec(
        name="downward",
        family="Planning",
        language="PDDL",
        emits="a PDDL domain (types, predicates, actions with preconditions and effects) and a problem "
        "(objects, initial state, goal).",
        authority="reachability in the transition system: Fast Downward finds plans or proves none exist; "
        "VAL independently validates plans.",
        feedback="the plan with its cost and VAL's validation, or translator/parser errors, or VAL's "
        "failed-precondition repair advice for a plan you supplied.",
        use="task planning with complex action dynamics: logistics, robotics, puzzles, workflows.",
        guidance=(
            "Classical PDDL (STRIPS/ADL, typing, negative preconditions, conditional effects, derived predicates, "
            "action costs with (:metric minimize (total-cost))); no durative actions or numeric fluents. "
            "Put the DOMAIN in `code` and the PROBLEM in `problem` (or both, one after the other, in `code`). Optional `mode`: 'satisficing' "
            "(default; LAMA, fast, any plan) or 'optimal' (A* with LM-cut; proves the plan has minimal cost; "
            "no conditional effects or derived predicates). Optional `plan`: one action per line, e.g. "
            "'(pick-up a)'; if given, nothing is searched - VAL checks your plan instead.\n"
            "Verdicts: sat = a plan was found (validated by VAL; see details.model); optimal = an optimal plan "
            "was found; unsat = the goal is provably unreachable; unknown = search limits hit; "
            "error = the PDDL did not parse or uses unsupported features. When checking a supplied `plan`: "
            "proved = it is valid, refuted = it is invalid (the output and details.counterexample say which "
            "precondition failed or which goal is unmet)."
        ),
        example=(
            "(define (domain switch) (:requirements :strips)\n"
            "  (:predicates (on) (off))\n"
            "  (:action turn-on :precondition (off) :effect (and (on) (not (off)))))\n"
            "problem: (define (problem p) (:domain switch) (:init (off)) (:goal (on)))"
        ),
        inputs={
            "problem": "The PDDL problem file (objects, :init, :goal).",
            "mode": "Optional: 'satisficing' (default) or 'optimal'.",
            "plan": "Optional plan to validate instead of searching, one '(action args)' per line.",
        },
        optional=["mode", "plan"],
    )

    def run(self, code: str, timeout: float, problem: str = "", mode: str = "", plan: str = "", **inputs: str) -> Result:
        if not problem.strip():  # both in `code` (e.g. from one fenced block): split them
            code, problem = _split_domain_problem(code)
        if not code.strip():
            return Result(Verdict.ERROR, "empty domain: `code` must be the PDDL domain (define (domain ...) ...)")
        if not problem.strip():
            return Result(Verdict.ERROR, "missing `problem` input: pass the PDDL problem next to the domain in `code`")
        mode = (mode or "satisficing").strip().lower()
        if mode not in ALIASES:
            return Result(Verdict.ERROR, f"unknown mode {mode!r}; use 'satisficing' or 'optimal'")
        with workdir({"domain.pddl": code, "problem.pddl": problem}) as d:
            if plan.strip():
                steps = _normalize_plan(plan)
                malformed = _plan_problems(code, steps)
                if malformed:  # VAL would only say "Bad plan description!"
                    report = "\n".join(malformed)
                    return Result(Verdict.REFUTED, "the plan does not fit the domain:\n" + report,
                                  {"validated": False, "mode": "validate",
                                   "counterexample": {"malformed_steps": malformed, "report": report}})  # fmt: skip
                (d / "sas_plan").write_text(steps)
                return self._check_plan(d, timeout)
            deadline = time.monotonic() + timeout
            proc = self._plan(d, ["--alias", ALIASES[mode]], [], deadline)
            complete = mode == "optimal"  # A* + LM-cut: complete, with safe dead ends
            if proc.returncode == 12 and not complete and deadline - time.monotonic() > 3:
                # We don't rely on LAMA's failure as a proof. Eager greedy
                # search with FF (whose dead ends are safe) is complete: it
                # settles unsolvability or finds a plan.
                proc = self._plan(d, [], ["--search", "eager_greedy([ff()])"], deadline)
                complete = True
            if proc.timed_out or re.search(r"exit code: -(24|9)\b", proc.out):  # killed by the time limit
                return timed_out(proc, "time limit reached (in translation or search)\n" + _tail(proc.out, 8))
            details = {"mode": mode, "exit_code": proc.returncode}
            rc = proc.returncode
            if rc in _PLAN_FOUND and (d / "sas_plan").exists():
                return self._plan_found(d, mode, details)
            # Fast Downward exits 12 for every failed search; only a complete
            # search that exhausted the state space proves unsolvability.
            exhausted = rc == 12 and complete and "Completely explored state space" in proc.out
            if rc in _UNSOLVABLE or exhausted:
                undeclared = _undeclared(code, problem)
                if undeclared:  # e.g. a typo in an object name makes the goal unreachable
                    return Result(Verdict.ERROR, "the task is malformed, so 'unsolvable' would be misleading:\n"
                                  + "\n".join(undeclared), {**details, "undeclared": undeclared})  # fmt: skip
                return Result(Verdict.UNSAT, "goal is unreachable: the planner proved the task unsolvable", details)
            if rc in _LIMITS:
                return Result(Verdict.UNKNOWN, "search hit a limit without a plan:\n" + _tail(proc.out, 15), details)
            if rc in _UNSUPPORTED:
                hint = " (try mode 'satisficing')" if mode == "optimal" else ""
                why = [ln.strip() for ln in proc.out.splitlines() if "support" in ln and "Tried to use" not in ln]
                return Result(Verdict.ERROR, f"unsupported PDDL feature for this planner{hint}:\n"
                              + ("\n".join(why) or _errors(proc.out)), details)  # fmt: skip
            message = _errors(proc.out)
            malformed = _undeclared(code, problem)
            if malformed:  # name the problem precisely instead of the translator's crash
                message = "\n".join(malformed) + "\n\n" + message
            if re.search(r"Invalid requirement.*(durative|numeric|fluents|time|continuous)", proc.out, re.S):
                message = ("Fast Downward is a classical planner: durative actions, numeric fluents (other than "
                           "action costs via total-cost) and continuous change are not supported.\n" + message)
            return Result(Verdict.ERROR, message, details)

    @staticmethod
    def _plan(d, driver_opts: list, search_opts: list, deadline: float):
        """One Fast Downward call within what is left of the time budget."""
        left = max(1, int(deadline - time.monotonic() - 2))
        # A memory cap makes a huge search stop with "out of memory" (-> unknown) before the container's limit.
        cmd = FD + driver_opts + ["--overall-time-limit", f"{left}s", "--overall-memory-limit", PLANNER_MEMORY,
                                  "--plan-file", "sas_plan",
                                  "domain.pddl", "problem.pddl"] + search_opts  # fmt: skip
        return sh(cmd, cwd=d, timeout=left + 10)

    def _plan_found(self, d, mode: str, details: dict) -> Result:
        text = (d / "sas_plan").read_text()
        steps = [ln.strip() for ln in text.splitlines() if ln.strip() and not ln.startswith(";")]
        cost = re.search(r";\s*cost\s*=\s*(\d+)", text)
        details.update(model=steps, cost=int(cost.group(1)) if cost else len(steps))
        val = sh(["Validate", "-v", "domain.pddl", "problem.pddl", "sas_plan"], cwd=d, timeout=30)
        valid = _val_valid(val.out)
        details["validated"] = valid
        verdict = Verdict.OPTIMAL if mode == "optimal" else Verdict.SAT
        lines = [f"plan ({len(steps)} steps, cost {details['cost']}):", *steps]
        if valid is True:
            lines.append("VAL: plan valid")
        elif valid is False:
            # The planner and the validator disagree: don't vouch for the plan.
            verdict = Verdict.UNKNOWN
            lines.append("VAL rejected the plan the planner found:\n" + _val_report(val.out))
        else:
            lines.append("VAL could not check this plan (unsupported features?):\n" + _tail(val.out, 10))
        return Result(verdict, "\n".join(lines), details)

    def _check_plan(self, d, timeout: float) -> Result:
        val = sh(["Validate", "-v", "domain.pddl", "problem.pddl", "sas_plan"], cwd=d, timeout=timeout)
        if val.timed_out:
            return timed_out(val)
        valid = _val_valid(val.out)
        details = {"validated": valid, "mode": "validate"}
        if valid is True:
            return Result(Verdict.PROVED, "VAL: plan valid (executes and reaches the goal)", details)
        if valid is False:
            report = _val_report(val.out)
            counterexample = {**_val_failure(val.out), "report": report}
            return Result(Verdict.REFUTED, "VAL: plan invalid\n" + report, {**details, "counterexample": counterexample})
        return Result(Verdict.ERROR, "VAL could not check the plan:\n" + _tail(val.out), details)


def _val_valid(out: str):
    if "Plan valid" in out:
        return True
    if any(s in out for s in ("Plan invalid", "Plan failed", "Goal not satisfied", "Bad plan")):
        return False
    return None


def _val_report(out: str) -> str:
    """VAL's verbose trace from the first step on: state changes, the failing
    step, and its repair advice (e.g. which precondition to make true)."""
    starts = ("Checking next happening", "Plan failed", "Goal not satisfied", "Plan valid", "Bad plan")
    lines = [ln.strip() for ln in out.splitlines() if ln.strip()]
    first = next((i for i, ln in enumerate(lines) if ln.startswith(starts)), None)
    if first is None:
        return _tail(out, 20)
    kept = [ln for ln in lines[first:] if ln not in ("Failed plans:", "Successful plans:", "sas_plan")]
    return "\n".join(kept[-60:])


def _split_domain_problem(text: str) -> tuple:
    """(domain, problem) when ``text`` holds both a (define (domain ..)) and a (define (problem ..)) form."""
    forms, depth, start = [], 0, None
    masked = re.sub(r";[^\n]*", lambda m: " " * len(m.group()), text)
    for i, ch in enumerate(masked):
        if ch == "(":
            if depth == 0:
                start = i
            depth += 1
        elif ch == ")" and depth:
            depth -= 1
            if depth == 0 and start is not None:
                forms.append(text[start : i + 1])
    kind = lambda f: (re.match(r"\(\s*define\s*\(\s*(domain|problem)\b", f, re.I) or [None, None])[1]  # noqa: E731
    domains = [f for f in forms if (kind(f) or "").lower() == "domain"]
    problems = [f for f in forms if (kind(f) or "").lower() == "problem"]
    if len(domains) == 1 and len(problems) == 1:
        return domains[0], problems[0]
    return text, ""


def _val_failure(out: str) -> dict:
    """VAL's verdict as data: the failing step and its unsatisfied preconditions, or the unmet goals."""
    failure: dict = {}
    m = re.search(r"^(\(.*\)) has an unsatisfied precondition at time (\d+)", out, re.M)
    advice = re.findall(r"^\(Set (\(.*?\)) to (true|false)\)", out, re.M)
    if m:
        failure.update(failed_step=int(m.group(2)), action=m.group(1),
                       unsatisfied=[f if v == "true" else f"(not {f})" for f, v in advice])
    elif "Goal not satisfied" in out:
        failure["unmet_goals"] = [f if v == "true" else f"(not {f})" for f, v in advice]
    return failure


def _plan_problems(domain: str, plan: str) -> list:
    """Steps naming an action the domain lacks, or with the wrong number of arguments."""
    try:
        tree = _sexprs(domain)
    except Exception:
        return []
    arity = {}
    for item in tree:
        if isinstance(item, list) and item and item[0] == "define":
            for part in item:
                if isinstance(part, list) and len(part) > 1 and part[0] == ":action" and isinstance(part[1], str):
                    params = part[part.index(":parameters") + 1] if ":parameters" in part else []
                    arity[part[1]] = len([x for x in _names(params) if isinstance(x, str) and x.startswith("?")])
    if not arity:
        return []
    problems = []
    for i, line in enumerate(plan.splitlines(), 1):
        words = line.strip().strip("()").lower().split()
        if not words:
            continue
        name, args = words[0], words[1:]
        if name not in arity:
            problems.append(f"step {i}: unknown action {name!r} (the domain has: {', '.join(sorted(arity))})")
        elif len(args) != arity[name]:
            problems.append(f"step {i}: {name} takes {arity[name]} argument(s), got {len(args)}: {line.strip()}")
    return problems


def _normalize_plan(plan: str) -> str:
    """One `(action args)` per line, as VAL expects; also accepts `0: (a b)` and bare `a b` lines."""
    lines = []
    for raw in plan.splitlines():
        line = raw.split(";", 1)[0].strip()
        line = re.sub(r"^\d+(\.\d+)?\s*:\s*", "", line)  # step numbers / timestamps
        line = re.sub(r"\s*\[\d+(\.\d+)?\]\s*$", "", line)  # durations
        if line:
            lines.append(line if line.startswith("(") else f"({line})")
    return "\n".join(lines) + "\n"


def _sexprs(text: str) -> list:
    """Parse PDDL into nested lists of lowercase atoms (comments dropped)."""
    tokens = re.findall(r"[()]|[^\s()]+", re.sub(r";[^\n]*", "", text).lower())
    stack: list = [[]]
    for tok in tokens:
        if tok == "(":
            stack.append([])
        elif tok == ")":
            if len(stack) > 1:
                done = stack.pop()
                stack[-1].append(done)
        else:
            stack[-1].append(tok)
    return stack[0]


def _section(tree: list, key: str) -> list:
    for item in tree:
        if isinstance(item, list) and item and item[0] == "define":
            for part in item:
                if isinstance(part, list) and part and part[0] == key:
                    return part[1:]
    return []


def _names(items: list) -> set:
    """Names from a typed list `a b - type c`, without the types."""
    out, skip = set(), False
    for x in items:
        if isinstance(x, str):
            if x == "-":
                skip = True
            elif skip:
                skip = False
            else:
                out.add(x)
    return out


_KEYWORDS = {"and", "or", "not", "imply", "exists", "forall", "when", "=", "preference", "always", "sometime",
             "within", "at-most-once", "sometime-after", "sometime-before", "always-within", "hold-during"}  # fmt: skip


def _undeclared(domain: str, problem: str) -> list:
    """Predicates and objects used in :init / :goal but declared nowhere, or with the wrong arity (best effort)."""
    try:
        dom, prob = _sexprs(domain), _sexprs(problem)
    except Exception:
        return []
    predicates = {p[0] for p in _section(dom, ":predicates") if isinstance(p, list) and p}
    arity = {p[0]: len(_names(p[1:])) for p in _section(dom, ":predicates") if isinstance(p, list) and p}
    functions = {f[0] for f in _section(dom, ":functions") if isinstance(f, list) and f}
    objects = _names(_section(dom, ":constants")) | _names(_section(prob, ":objects"))
    if not predicates:
        return []
    found: list = []

    def walk(expr, bound: set) -> None:
        if not isinstance(expr, list) or not expr or not isinstance(expr[0], str):
            return
        head = expr[0]
        if head == "at" and len(expr) == 3 and isinstance(expr[1], str) and re.fullmatch(r"[\d.]+", expr[1]):
            walk(expr[2], bound)  # a timed initial literal: (at 10 (fact))
            return
        if head in ("exists", "forall") and len(expr) > 2 and isinstance(expr[1], list):
            walk(expr[2], bound | {v for v in _names(expr[1]) if v.startswith("?")})
            return
        if head in _KEYWORDS:
            for sub in expr[1:]:
                walk(sub, bound)
            return
        if head not in predicates and head not in functions:
            found.append(f"undeclared predicate or function: {head}")
        elif head in arity and len(expr) - 1 != arity[head]:
            found.append(f"{head} takes {arity[head]} argument(s), got {len(expr) - 1}: ({' '.join(map(str, expr))})")
        for arg in expr[1:]:
            if isinstance(arg, str) and not arg.startswith("?") and arg not in objects and not re.fullmatch(r"-?[\d.]+", arg):
                found.append(f"undeclared object: {arg} (in ({' '.join(map(str, expr))}))")
            elif isinstance(arg, list):
                walk(arg, bound)

    for fact in _section(prob, ":init"):
        walk(fact, set())
    for goal in _section(prob, ":goal"):
        walk(goal, set())
    return list(dict.fromkeys(found))


def _errors(out: str) -> str:
    """Translator/search errors without the driver's boilerplate."""
    noise = ("INFO", "Running ", "callstring", "translator ", "search ", "planner ", "remaining time",
             "Done!", "Parsing...", "Normalizing", "Instantiating", "Computing", "Generating", "Building",
             "Simplifying", "Translating", "Processing", "Detecting", "Reordering", "Writing", "Parsing:")
    lines = [ln for ln in out.splitlines() if ln.strip() and not ln.strip().startswith(noise)]
    # A translator crash arrives as a bytes-literal traceback; keep just its final exception line.
    crash = re.search(r"b'Traceback(.*?)'", out, re.S)
    if crash:
        last = [part.strip() for part in crash.group(1).split("\\n") if part.strip()][-1]
        lines = [ln for ln in lines if not ln.startswith("b'Traceback")] + [f"translator error: {last}"]
    if "Unbound effect variables" in out or "Unbound" in out and "variables" in out:
        lines.insert(0, "an action's precondition or effect uses a variable that is not in its :parameters")
    return _tail("\n".join(lines) or out, 30)


ADAPTER = Downward()
