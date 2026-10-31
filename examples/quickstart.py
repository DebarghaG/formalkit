"""Run programs through formal backends directly - no LLM involved."""

import formalkit

z3 = formalkit.backend("z3")  # starts the container on first use

# Prove "x > 5 implies 2x > 10" by refuting its negation.
r = z3.run("""
(declare-const x Int)
(assert (> x 5))
(assert (not (> (* 2 x) 10)))
(check-sat)
""")
print(r.verdict)        # unsat  -> the claim is proved
print(r.decisive)       # True
print(r.feedback())     # what an LLM would see

# Every backend speaks the same protocol.
print(z3.spec.describe())
