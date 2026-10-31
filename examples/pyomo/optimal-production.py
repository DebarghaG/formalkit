# Two products sharing machine hours; maximize profit.
import pyomo.environ as pyo

model = pyo.ConcreteModel()
model.chairs = pyo.Var(domain=pyo.NonNegativeIntegers)
model.tables = pyo.Var(domain=pyo.NonNegativeIntegers)
model.carpentry = pyo.Constraint(expr=3 * model.chairs + 5 * model.tables <= 60)
model.finishing = pyo.Constraint(expr=2 * model.chairs + 2 * model.tables <= 28)
model.profit = pyo.Objective(expr=20 * model.chairs + 35 * model.tables, sense=pyo.maximize)
