from __future__ import annotations

import re

from formalkit.core import Result, Spec, Verdict
from formalkit.server import Adapter, sh, timed_out, workdir

# Runs main() with IDP-Z3's own print capture; any exception becomes a
# single "IDP-ERROR:" line instead of a parser traceback.
#
# IDP-Z3's optimize() takes Z3's answer and then tries up to 10 times to find
# a strictly better value; when every try succeeds (an unbounded objective)
# it silently returns the 10th value. The same method is installed here, but
# that case - and Z3 reporting an infinite bound - is flagged on stderr
# ("IDP-UNPROVEN:") instead of passing as optimal.
DRIVER = """
import sys
from idp_engine import IDP
from idp_engine.Theory import Theory

PATCH = '''
def optimize(self, term, minimize=True):
    assert term in self.assignments, f'Optimization term: "{term}" not found in vocabulary (Tip: have you forgotten brackets? e.g. P()).'
    term = self.assignments[term]
    decl = term.symbol_decl
    assert len(decl.codomain.root_set) == 1 and decl.codomain.root_set[0] in (INT_SETNAME, REAL_SETNAME), f'Incorrect optimization term: "{term}", term must be of type {INT} or {REAL}.'
    sentence = term.sentence
    s = sentence.translate(self)
    if self.ignored_laws:
        solver = self.optimize_solver_reified
        solver.push()
        self._add_assignment_ignored(solver)
    else:
        solver = self.optimize_solver
        solver.push()
        self._add_assignment(solver)
    handle = solver.minimize(s) if minimize else solver.maximize(s)
    res = solver.check()
    assert res == sat, "Optimization requires satisfiable specification"
    proven = "oo" not in str(handle.value())
    val = solver.model().eval(s)
    for i in range(0, 10):
        solver.add(s < val if minimize else val < s)
        if solver.check() == sat:
            val = solver.model().eval(s)
        else:
            break
    else:
        proven = False
    solver.pop()
    if not proven:
        sys.stderr.write(f"IDP-UNPROVEN: {sentence}\\\\n")
    val_IDP = z3_to_idp(val, sentence.type)
    if val_IDP is not None:
        self.assert_(str(sentence), val_IDP, S.GIVEN)
        ass = str(EQUALS([sentence, val_IDP]))
        if ass in self.assignments:
            self.assert_(ass, True, S.GIVEN)
    return self
'''
namespace = Theory.optimize.__globals__
namespace.setdefault("sys", sys)
exec(PATCH, namespace)
Theory.optimize = namespace["optimize"]

try:
    source = open("theory.idp", encoding="utf-8").read()
    # Models often write Prolog/ASP-style `%` line comments; IDP's are `//` (and `%` is modulo).
    source = "\\n".join("//" + l.lstrip()[1:] if l.lstrip().startswith("%") else l for l in source.split("\\n"))
    if not source.strip():
        raise ValueError("empty input: send a vocabulary, a theory and procedure main()")
    kb = IDP.from_str(source)
    if "main" not in getattr(kb, "procedures", {"main": None}):
        raise ValueError("no `procedure main() {...}` found: add one that prints the inference results")
    out = kb.execute(capture_print=True)
    print(out or "")
except BaseException as exc:
    print(f"IDP-ERROR: {type(exc).__name__}: {exc}", file=sys.stderr)
    sys.exit(1)
"""

_NO_MODEL = ("No models.", "Not satisfiable.", "unsat")
_OPTIMIZE = re.compile(r"\b(minimize|maximize)\s*\(")


class Idp(Adapter):
    spec = Spec(
        name="idp",
        family="KB",
        language="FO(.) in IDP-Z3 syntax",
        emits="a vocabulary (types, predicates, functions), a theory of FO(.) axioms and inductive definitions, an optional structure with known facts, and a main() procedure naming the inference.",
        authority="FO(.) semantics: model expansion, propagation, model checking and optimization over one shared knowledge base.",
        feedback="the printed result of main(): models, propagated consequences, sat/unsat, optimal models; or the parse/type error.",
        use="one domain model answering many queries: configuration, eligibility rules, puzzles, consequence finding.",
        guidance=(
            "Send a complete .idp file: `vocabulary V {...}`, `theory T:V {...}`, optionally `structure S:V {...}`, "
            "and `procedure main() {...}` that prints results, e.g. pretty_print(model_expand(T, S, max=5)), "
            "pretty_print(model_propagate(T, S)), print(model_check(T, S)), pretty_print(minimize(T, S, term=\"cost()\")). "
            "Comments are `//` or `/* */`. Syntax: `type Color := {red, green}`, `p: Color -> Bool`, `f: () -> Int`; quantifiers `!x in T: ...` / "
            "`?x in T: ...`; connectives & | ~ => <=>; definitions `{ !x in T: q(x) <- p(x). }`; constants are "
            "applied as c(). Verdict: unsat if any inference reports no model (\"No models.\", \"Not satisfiable.\", "
            "unsat), optimal for a successful minimize/maximize, sat otherwise; error on parse/type errors. "
            "To PROVE a claim, add its negation as an axiom and print(model_check(T)): unsat proves it."
        ),
        example=(
            "vocabulary V { type Person := {ann, bob}  smokes: Person -> Bool  friends: Person * Person -> Bool }\n"
            "theory T:V { !x, y in Person: friends(x, y) & smokes(x) => smokes(y).  smokes(ann).  ~smokes(bob). }\n"
            "structure S:V { friends := {(ann, bob)}. }\n"
            "procedure main() { print(model_check(T, S)) }"
        ),
    )

    def run(self, code: str, timeout: float, **inputs: str) -> Result:
        with workdir({"theory.idp": code, "driver.py": DRIVER}) as d:
            proc = sh(["python3", "driver.py"], cwd=d, timeout=timeout)
        if proc.timed_out:
            return timed_out(proc, "IDP-Z3 did not finish within the time limit")
        out = proc.stdout.strip()
        error = next((ln[len("IDP-ERROR: "):] for ln in proc.stderr.splitlines() if ln.startswith("IDP-ERROR: ")), None)
        if error and "requires satisfiable specification" in error:
            return Result(Verdict.UNSAT, f"{out}\nNot satisfiable (optimization over an unsatisfiable theory).".strip())
        if error or proc.returncode != 0:
            return Result(Verdict.ERROR, "\n".join(filter(None, [out, error or proc.stderr.strip()])))
        lines = {ln.strip() for ln in out.splitlines()}
        if lines & set(_NO_MODEL):
            return Result(Verdict.UNSAT, out)
        if not out:
            return Result(Verdict.ERROR, "main() printed nothing; print the inference results, e.g. pretty_print(model_expand(T)).")
        unproven = [ln[len("IDP-UNPROVEN: "):] for ln in proc.stderr.splitlines() if ln.startswith("IDP-UNPROVEN: ")]
        if unproven:  # the objective is unbounded (or optimality could not be established)
            note = f"optimality not proven for {', '.join(unproven)}: the objective appears unbounded"
            return Result(Verdict.SAT, f"{out}\n{note}", {"model": out, "unbounded": True})
        verdict = Verdict.OPTIMAL if _OPTIMIZE.search(code) else Verdict.SAT
        return Result(verdict, out, {"model": out})  # the printed inference results


ADAPTER = Idp()
