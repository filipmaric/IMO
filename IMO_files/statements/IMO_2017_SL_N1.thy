section\<open>Number theory problems\<close>

subsection \<open>IMO 2017 SL - N1\<close>

theory IMO_2017_SL_N1
imports Complex_Main
begin
(*
lemma square_mod_3:
  fixes x :: nat
  shows "(x * x) mod 3 = 0 \<longleftrightarrow> x mod 3 = 0"
  sorry

lemma square_mod_3_not_2:
  fixes s :: nat
  shows "(s * s) mod 3 \<noteq> 2"
  sorry

lemma not_square_3: 
  shows "\<not> (\<exists> s::nat. s * s = 3)"
  sorry

lemma not_square_6: 
  shows "\<not> (\<exists> s::nat. s * s = 6)"
  sorry

lemma not_square_7: 
  shows "\<not> (\<exists> s::nat. s * s = 7)"
  sorry

lemma not_square_10: 
  shows "\<not> (\<exists> s::nat. s * s = 10)"
  sorry

lemma not_square_13: 
  shows "\<not> (\<exists> s::nat. s * s = 13)"
  sorry

lemma consecutive_squares_mod_3:
  fixes t :: nat
  shows "{(t + 1)\<^sup>2 mod 3, (t + 2)\<^sup>2 mod 3, (t + 3)\<^sup>2 mod 3} = {0, 1}"
  sorry

definition eventually_periodic :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "eventually_periodic a \<longleftrightarrow> (\<exists> p > 0. \<exists> n0. \<forall> n \<ge> n0. a (n + p) = a n)"

lemma initial_condition:
  fixes a :: "nat \<Rightarrow> 'a"
  assumes "\<forall> n. a (n + 1) = f (a n)" "a n1 = a n2"
  shows "a (n1 + k) = a (n2 + k)"
  sorry

lemma two_same_periodic:
  fixes a :: "nat \<Rightarrow> 'a"
  assumes "\<forall> n. a (n + 1) = f (a n)" "n1 < n2" "a n1 = a n2"
  shows "eventually_periodic a"
  sorry

lemma eventually_periodic_repeats:        
  fixes a :: "nat \<Rightarrow> 'a"
  assumes "\<forall> n \<ge> n0. a (n + p) = a n"
  shows "\<forall> k. a (n0 + k * p) = a n0"
  sorry

lemma infinite_periodic:
  fixes a :: "nat \<Rightarrow> 'a"
  assumes "\<forall> n. a (n + 1) = f (a n)"
  shows "(\<exists> A. infinite {n. a n = A}) \<longleftrightarrow> eventually_periodic a"
  sorry

definition eventually_increasing :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "eventually_increasing a \<longleftrightarrow> (\<exists> n0. \<forall> n \<ge> n0. a n < a (n + 1))"

lemma eventually_increasing:
  shows "eventually_increasing a \<longleftrightarrow> (\<exists> n0. \<forall> i j. n0 \<le> i \<and> i < j \<longrightarrow> a i < a j)"
  sorry

lemma increasing_non_periodic:
  assumes "eventually_increasing a"
  shows "\<not> eventually_periodic a"
  sorry
*)
definition sqrt_nat :: "nat \<Rightarrow> nat" where 
  "sqrt_nat x = (THE s. x = s * s)"
(*
lemma sqrt_nat:
  fixes x s :: nat
  assumes "x = s * s"
  shows "sqrt_nat x = s"
  sorry

lemma Least_nat_in:
  fixes A :: "nat set"
  assumes "A \<noteq> {}"
  shows "(LEAST x. x \<in> A) \<in> A"
  sorry

lemma Least_nat_le:
  fixes A :: "nat set"
  assumes "A \<noteq> {}"
  shows "\<forall> x \<in> A. (LEAST x. x \<in> A) \<le> x"
  sorry
*)
theorem IMO_2017_SL_N1:
  fixes a :: "nat \<Rightarrow> nat"
  assumes "\<forall> n. a (n + 1) = (if (\<exists> s. a n  = s * s) 
                                     then sqrt_nat (a n) 
                                     else (a n) + 3)"
         and  "a 0 > 1"
  shows "(\<exists> A. infinite {n. a n = A}) \<longleftrightarrow> a 0 mod 3 = 0"
  sorry

end