subsection \<open>IMO 2006 SL - A2\<close>

theory IMO_2006_SL_A2
imports Complex_Main
begin

theorem IMO_2006_SL_A2:
  fixes a :: "nat \<Rightarrow> real"
  assumes "a 0 = -1" "\<forall> n \<ge> 1. (\<Sum> k < Suc n. a (n - k) / (k + 1)) = 0" "n \<ge> 1"
  shows "a n > 0"
  using \<open>n \<ge> 1\<close>
  sorry

end