section\<open>Algebra problems\<close>

subsection \<open>IMO 2008 SL - A1\<close>

theory IMO_2008_SL_A1
imports Complex_Main
begin

theorem IMO_2008_SL_A1:
  fixes f :: "real \<Rightarrow> real"
  assumes "\<forall> p q r s :: real. p > 0 \<and> q > 0 \<and> r > 0 \<and> s > 0 \<and> pq = rs \<and> 
   ((f p)^2 + (f q)^2) / ((f r^2) + (f s^2)) = (p^2 + q^2) / (r^2 + s^2)"
  shows "(\<forall> x > 0. f x = x) \<or> (\<forall> x > 0. f x = 1 / x)" 
  sorry

end