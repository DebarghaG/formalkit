theorem add_comm' (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ n ih => skip
