import cpmpy as cp

x = cp.intvar(0, 3, name="x")
m = cp.Model(x > 1)  # wrong name: the tool needs `model`
