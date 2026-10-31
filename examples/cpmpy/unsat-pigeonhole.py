# Claim: 4 pigeons cannot sit in 3 holes, one per hole. unsat proves it.
import cpmpy as cp

hole = cp.intvar(1, 3, shape=4, name="hole")
model = cp.Model(cp.AllDifferent(hole))
