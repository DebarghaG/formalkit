# No objective: any feasible point answers the question.
import pyomo.environ as pyo

model = pyo.ConcreteModel()
model.x = pyo.Var(bounds=(0, 10))
model.y = pyo.Var(bounds=(0, 10))
model.c1 = pyo.Constraint(expr=model.x + model.y == 7)
model.c2 = pyo.Constraint(expr=model.x - model.y >= 1)
