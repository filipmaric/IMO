section \<open>Number theory problems\<close>

subsection \<open>IMO 2018 SL - N5\<close>

theory IMO_2018_SL_N5
imports Main
begin

definition perfect_square :: "int \<Rightarrow> bool" where
  "perfect_square s \<longleftrightarrow> (\<exists> r. s = r * r)"
(*
lemma perfect_square_root_pos:
  assumes "perfect_square s"
  shows "\<exists> r. r \<ge> 0 \<and> s = r * r"
  sorry

lemma not_perfect_square_15:
  fixes q::int
  shows "q^2 \<noteq> 15"
  sorry

lemma not_perfect_square_12:
  fixes q::int
  shows "q^2 \<noteq> 12"
  sorry

lemma not_perfect_square_8:
  fixes q::int
  shows "q^2 \<noteq> 8"
  sorry

lemma not_perfect_square_7:
  fixes q::int
  shows "q^2 \<noteq> 7"
  sorry

lemma not_perfect_square_5:
  fixes q::int
  shows "q^2 \<noteq> 5"
  sorry

lemma not_perfect_square_3:
  fixes q::int
  shows "q^2 \<noteq> 3"
  sorry
*)
lemma IMO2018SL_N5_lemma:
  fixes s a b c d :: int
  assumes "s^2 = a^2 + b^2" "s^2 = c^2 + d^2" "2*s = a^2 - c^2" 
  assumes  "s > 0" "a \<ge> 0" "d \<ge> 0" "b \<ge> 0" "c \<ge> 0" "b > 0 \<or> c > 0" "b \<ge> c" 
  shows False
  sorry

theorem IMO2018SL_N5:
  fixes x y z t :: int
  assumes pos: "x > 0" "y > 0" "z > 0" "t > 0"
  assumes eq: "x*y - z*t = x + y" "x + y = z + t"
  shows " \<not> (perfect_square (x*y) \<and> perfect_square (z*t))"
  sorry

end