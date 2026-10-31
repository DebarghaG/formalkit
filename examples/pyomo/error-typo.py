import pyomo.environ as pyo

model = pyo.ConcreteModel()
model.x = pyo.Var(domain=pyo.NonNegativeReals)
model.c = pyo.Constraint(expr=model.y <= 5)
