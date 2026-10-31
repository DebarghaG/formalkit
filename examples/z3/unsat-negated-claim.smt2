; claim: x > 5 implies 2x > 10. Assert the negation; unsat proves it.
(declare-const x Int)
(assert (> x 5))
(assert (not (> (* 2 x) 10)))
(check-sat)
