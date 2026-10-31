"""Reference implementations of the ways LLMs and formal tools are combined.

Each pattern is a short, readable function over the same few pieces -
:class:`~formalkit.LLM`, :class:`~formalkit.Backend`, :class:`~formalkit.State`,
:class:`~formalkit.Result`, :class:`~formalkit.Step` - so they compose and are
easy to adapt. The tool-calling loop itself is :class:`formalkit.Agent`;
learning from formal feedback lives in :mod:`formalkit.learn`.

By the role the formal backend plays:

``generate``    the model writes whole artifacts (or, with ``pin``, only the
                hole of a fixed statement): refine, translate_and_solve,
                formalize, pin, sample, vote, route,
                backtranslate, cycle_consistency, conjecture
``prove``       holes, search and repair, with the backend as checker and
                search environment: sketch_and_fill, decompose, step_search,
                llm_steps, llm_close, mix, automation, suggest, probe,
                repair, tactic_swap, localize
``synthesize``  propose, check, learn from the failure:
                cegis, propose_until_proved, ask_with_feedback, houdini,
                assume_and_discharge
``control``     the solver in control, the model as a subroutine:
                soft_facts, instantiate, lns, llm_neighborhood
``check``       the backend as judge of artifacts: smt_equivalent,
                lean_equivalent, unique, differential, label, best_of
"""

from formalkit.patterns.check import (
    Differential,
    best_of,
    differential,
    label,
    lean_equivalent,
    smt_equivalent,
    unique,
)
from formalkit.patterns.control import Instantiated, Neighborhoods, Scored, instantiate, llm_neighborhood, lns, soft_facts
from formalkit.patterns.generate import (
    Consensus,
    Conjecture,
    Vote,
    backtranslate,
    conjecture,
    consensus,
    cycle_consistency,
    formalize,
    pin,
    pinned,
    refine,
    route,
    sample,
    translate_and_solve,
    vote,
)
from formalkit.patterns.prove import (
    AUTOMATION,
    Filled,
    Search,
    automation,
    decompose,
    error_lines,
    holes,
    llm_close,
    llm_steps,
    localize,
    mix,
    probe,
    repair,
    sketch_and_fill,
    step_search,
    suggest,
    tactic_swap,
)
from formalkit.patterns.synthesize import (
    Loop,
    Pruned,
    ask_with_feedback,
    assume_and_discharge,
    cegis,
    houdini,
    propose_until_proved,
)

__all__ = [
    "AUTOMATION", "Conjecture", "Consensus", "consensus", "Differential", "Filled", "Instantiated", "Loop", "Neighborhoods", "Pruned",
    "Scored", "Search", "Vote", "ask_with_feedback", "assume_and_discharge", "automation", "backtranslate",
    "best_of", "cegis", "conjecture", "cycle_consistency", "decompose", "differential", "error_lines",
    "formalize", "holes", "pin", "pinned", "houdini", "instantiate", "label", "lean_equivalent", "llm_close", "llm_neighborhood",
    "llm_steps", "lns", "localize", "mix", "probe", "propose_until_proved", "refine", "repair", "route",
    "sample", "sketch_and_fill", "smt_equivalent", "soft_facts", "step_search", "suggest", "tactic_swap",
    "translate_and_solve", "unique", "vote",
]  # fmt: skip
