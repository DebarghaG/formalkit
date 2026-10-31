import Mathlib

theorem sum_sq_nonneg (a b : ℝ) : 0 ≤ a ^ 2 + b ^ 2 := by
  positivity

theorem my_irrational_sqrt_two : Irrational (Real.sqrt 2) := by
  simpa using irrational_sqrt_two
