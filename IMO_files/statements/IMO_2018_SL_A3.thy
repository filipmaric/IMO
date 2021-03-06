subsection \<open>IMO 2018 SL - A3\<close>

theory IMO_2018_SL_A3
imports Complex_Main

begin

theorem IMO2018SL_A3:
  fixes S :: "nat set"
  assumes "\<forall> x \<in> S. x > 0"
  shows "(\<exists> F G. F \<subseteq> S \<and> G \<subseteq> S \<and> F \<inter> G = {} \<and> (\<Sum>x\<in>F. 1/(rat_of_nat x)) = (\<Sum>x\<in>G.1/(rat_of_nat x))) \<or>
         (\<exists> r::rat. 0 < r \<and> r < 1 \<and> (\<forall> F \<subseteq> S. finite F \<longrightarrow> (\<Sum>x\<in>F. 1/(rat_of_nat x)) \<noteq> r))"
  sorry

end