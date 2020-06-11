subsection \<open>IMO 2018 SL - A4\<close>

theory IMO_2018_SL_A4
imports Complex_Main
begin

definition is_Max :: "'a::linorder set \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_Max A x \<longleftrightarrow> x \<in> A \<and> (\<forall> x' \<in> A. x' \<le> x)"

theorem IMO2018SL_A4:
  shows
  "is_Max {a 2018 - a 2017 | a::nat \<Rightarrow> real. a 0 = 0 \<and> a 1 = 1 \<and> (\<forall> n \<ge> 2. \<exists> k. 1 \<le> k \<and> k \<le> n \<and> a n = (\<Sum> i \<leftarrow> [n-k..<n]. a i) / real k)}
   (2016 / 2017^2)" (is "is_Max {?f a | a. ?P a} ?m")
  unfolding is_Max_def
  sorry

end