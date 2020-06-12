section\<open>Algebra problems\<close>

subsection \<open>IMO 2006 SL - A1\<close>

theory IMO_2006_SL_A1
imports Complex_Main
begin

theorem IMO_2006_SL_A1:
  fixes a :: "nat \<Rightarrow> real"
  assumes "\<forall> i \<ge> 0. (a (i + 1) = floor (a i) * (a i - floor (a i)))"
  shows "\<exists> i. a i = a (i + 2)"
  sorry

end