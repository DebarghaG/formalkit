"""formalkit: one interface between LLMs and formal tools.

SMT-LIB gave every SMT solver one input language and one answer vocabulary.
formalkit does the same one level up, for every kind of formal backend - SMT
and SAT solvers, theorem provers, ATPs, logic and answer-set programming,
planners, model checkers, CP/MILP solvers and program verifiers. Each runs
in its own Docker container behind one protocol:

    run(code) -> Result(verdict, output, details)

with ``verdict`` one of proved / refuted / sat / unsat / optimal / unknown /
error.

    import formalkit

    z3 = formalkit.backend("z3")
    print(z3.run("(declare-const x Int) (assert (> x 5)) (check-sat)").verdict)

    agent = formalkit.Agent(formalkit.LLM(openai_client, "gpt-5"), backends=["z3", "clingo"])
    print(agent.solve("Is there an integer greater than 5 and less than 3?"))
"""

from formalkit.agent import Agent, Answer, Step
from formalkit.client import Backend, Remote, State, backend, backends, compiled, portfolio, premises
from formalkit.core import Result, Spec, Verdict
from formalkit.evidence import Rejected, cited_or_last, nonvacuous
from formalkit.guard import Decision, Guard
from formalkit.library import Library
from formalkit.llm import LLM, extract_code
from formalkit.observe import Budget, BudgetExceeded, Event, Trace, observe
from formalkit.registry import BACKENDS

__version__ = "0.1.0"

__all__ = [
    "Agent",
    "Answer",
    "BACKENDS",
    "Backend",
    "Budget",
    "Decision",
    "BudgetExceeded",
    "Event",
    "Guard",
    "LLM",
    "Library",
    "Rejected",
    "Remote",
    "Result",
    "Spec",
    "State",
    "Step",
    "Trace",
    "Verdict",
    "backend",
    "backends",
    "cited_or_last",
    "compiled",
    "extract_code",
    "nonvacuous",
    "observe",
    "portfolio",
    "premises",
]
