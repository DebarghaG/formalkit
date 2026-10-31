-- #eval is fine for exploring, but a file that runs code while it is checked is never certified.
#eval 2 ^ 10
theorem pow_ten : 2 ^ 10 = 1024 := by decide
