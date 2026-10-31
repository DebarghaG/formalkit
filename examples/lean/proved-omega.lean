-- Core Lean, no Mathlib: fast to check.
theorem two_mul_gt (x : Nat) (h : 5 < x) : 10 < 2 * x := by
  omega
