section \<open>Algebra problems\<close>

subsection \<open>IMO 2018 SL - A1\<close>

theory IMO_2018_SL_A1
imports HOL.Rat

begin

theorem IMO2018SL_A1:
  fixes x y :: "rat" and f :: "rat \<Rightarrow> rat"
  assumes "f (x * x * (f y) * (f y)) = (f x) * (f x) * (f y)"
  shows "f x = 1"
  sorry

end