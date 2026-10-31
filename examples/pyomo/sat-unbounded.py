import pyomo.environ as pyo

model = pyo.ConcreteModel()
model.x = pyo.Var(domain=pyo.NonNegativeReals)
model.c = pyo.Constraint(expr=model.x >= 5)
model.obj = pyo.Objective(expr=model.x, sense=pyo.maximize)
