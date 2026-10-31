# Claim: the demand cannot be met within budget. Infeasibility proves it.
import pyomo.environ as pyo

model = pyo.ConcreteModel()
model.units = pyo.Var(domain=pyo.NonNegativeReals)
model.demand = pyo.Constraint(expr=model.units >= 100)
model.budget = pyo.Constraint(expr=12 * model.units <= 1000)
model.cost = pyo.Objective(expr=12 * model.units)
