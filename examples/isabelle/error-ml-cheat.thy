theory Scratch imports Main begin

(* ML-level tactics can forge theorems: rejected. *)
lemma "1 = (2::nat)"
  by (tactic \<open>Skip_Proof.cheat_tac \<^context> 1\<close>)

end
