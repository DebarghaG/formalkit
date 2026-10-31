import cpmpy as cp

values, weights, capacity = [10, 13, 7, 8], [5, 6, 3, 4], 10
take = cp.boolvar(shape=4, name="take")
model = cp.Model(cp.sum(take * weights) <= capacity, maximize=cp.sum(take * values))
