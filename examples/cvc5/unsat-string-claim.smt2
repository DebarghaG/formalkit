; claim: for strings, prefixing "ab" makes length >= 2. Negate it; unsat proves it.
(set-logic ALL)
(declare-const s String)
(assert (str.prefixof "ab" s))
(assert (not (>= (str.len s) 2)))
(check-sat)
