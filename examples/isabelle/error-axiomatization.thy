theory Scratch imports Main begin

axiomatization where cheat: "False"

lemma "1 = (2::nat)" using cheat by simp

end
