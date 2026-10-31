theory Scratch imports Main begin

(* Conjecture: append is commutative. Nitpick finds a counterexample. *)
lemma "xs @ ys = ys @ xs"
  nitpick
  oops

end
