"""The catalog of backends: name -> family, image, one-line summary.

Several backends may share one image (e.g. prover9 and mace4 ship
together); the container command picks the adapter.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Entry:
    name: str
    family: str
    image: str  # directory under docker/ and image name suffix
    summary: str
    docker_args: tuple = ()  # extra `docker run` options this backend needs


# Lake's comparator sandboxes the untrusted build with bubblewrap, which needs user namespaces
# and its own /proc: Docker's default seccomp/AppArmor profiles and /proc masking forbid that.
# All capabilities stay dropped and no-new-privileges stays on; the server runs unprivileged.
_NESTED_SANDBOX = ("--security-opt", "seccomp=unconfined", "--security-opt", "apparmor=unconfined",
                   "--security-opt", "systempaths=unconfined")  # fmt: skip


_ENTRIES = [
    # SAT and SMT
    Entry("z3", "SMT", "z3", "SMT-LIB 2.6 -> sat/unsat, models, unsat cores"),
    Entry("cvc5", "SMT", "cvc5", "SMT-LIB 2.6 -> sat/unsat, models, unsat cores, proofs"),
    Entry("kissat", "SAT", "sat", "DIMACS CNF -> satisfying assignment or DRAT-checked unsat"),
    # Interactive theorem provers
    Entry("lean", "ITP", "lean", "Lean 4 + Mathlib -> kernel-checked proofs certified by lake comparator",
          _NESTED_SANDBOX),
    Entry("isabelle", "ITP", "isabelle", "Isabelle/HOL theories -> checked proofs, subgoals, Sledgehammer, Nitpick"),
    Entry("metamath", "ITP", "metamath", "Metamath databases -> step-level proof verification"),
    # First-order and rule-based reasoning
    Entry("vampire", "FOL", "vampire", "TPTP -> proofs (SZS Theorem) or saturation/countermodels"),
    Entry("prover9", "FOL", "ladr", "Prover9 input -> resolution proofs"),
    Entry("mace4", "FOL", "ladr", "Prover9 input -> finite models and countermodels"),
    Entry("idp", "KB", "idp", "FO(.) knowledge bases (IDP-Z3) -> models, propagation, inconsistency"),
    Entry("prolog", "LP", "prolog", "SWI-Prolog facts/rules + queries -> answers, failures, errors"),
    Entry("problog", "LP", "problog", "ProbLog programs -> query probabilities"),
    # Answer set programming
    Entry("clingo", "ASP", "clingo", "ASP programs -> answer sets, optima, unsatisfiability"),
    # Planning and temporal logic
    Entry("downward", "Planning", "downward", "PDDL domain + problem -> validated plans or unsolvability"),
    Entry("spin", "LTL", "spin", "Promela + LTL -> property holds or counterexample trail"),
    # Constraint programming and optimization
    Entry("minizinc", "CP", "minizinc", "MiniZinc models -> solutions, optima, infeasibility"),
    Entry("cpmpy", "CP", "cpmpy", "CPMpy (OR-Tools CP-SAT) Python models -> solutions, optima"),
    Entry("pyomo", "MP", "pyomo", "Pyomo LP/MILP/QP models -> optima, bounds, infeasibility"),
    # Program verifiers and domain engines
    Entry("cbmc", "Verifier", "cbmc", "C programs with assertions -> bounded proofs or counterexample traces"),
    Entry("esbmc", "Verifier", "esbmc", "C/C++ programs -> bounded proofs or counterexample traces"),
    Entry("framac", "Verifier", "framac", "ACSL-annotated C -> WP proof obligations proved/unproved"),
    Entry("ultimate", "Verifier", "ultimate", "C programs -> Ultimate Automizer proofs or counterexamples"),
    Entry("ddar", "Domain", "ddar", "AlphaGeometry problems -> DD+AR derived facts and goal proofs"),
]

@dataclass(frozen=True)
class Virtual:
    """A backend assembled on the host from other backends (no image of its own)."""

    name: str
    family: str
    factory: str  # "module:function" returning a Backend
    summary: str


_VIRTUAL = [
    Virtual("pot", "IR", "formalkit.ir.pot:backend", "Proof of Thought JSON DSL, compiled to SMT-LIB for z3"),
]

BACKENDS: dict[str, Entry] = {e.name: e for e in _ENTRIES}
VIRTUAL: dict[str, Virtual] = {v.name: v for v in _VIRTUAL}
FAMILIES: tuple[str, ...] = tuple(dict.fromkeys(e.family for e in [*_ENTRIES, *_VIRTUAL]))


def entry(name: str) -> Entry:
    try:
        return BACKENDS[name]
    except KeyError:
        if name in VIRTUAL:
            raise KeyError(f"{name!r} is a virtual backend (built on the host from other backends); it has no image") from None
        raise KeyError(f"unknown backend {name!r}; known: {', '.join([*BACKENDS, *VIRTUAL])}") from None
