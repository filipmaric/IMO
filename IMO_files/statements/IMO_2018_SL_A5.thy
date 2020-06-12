subsection \<open>IMO 2018 SL - A5\<close>

theory IMO_2018_SL_A5
imports Complex_Main
begin

theorem IMO_2018_SL_A5:
  fixes f :: "real \<Rightarrow> real"
  assumes "\<forall> x > 0. \<forall> y > 0. (x + 1/x) * (f y) = f (x*y) + f (y / x)"
  shows "\<exists> C1 C2. \<forall> x > 0. f x = C1 * x + C2 / x"
  sorry

end
