theory Scratch imports Main begin

lemma rev_rev: "rev (rev xs) = xs"
  by simp

lemma length_append: "length (xs @ ys) = length xs + length ys"
  by (induct xs) auto

end
