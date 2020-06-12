section\<open>Algebra problems\<close>

subsection \<open>IMO 2006 SL - A2\<close>

theory IMO_2006_SL_A2_sol
imports Complex_Main
begin

lemma sum_remove_zero:
  fixes n :: nat
  assumes "n > 0"
  shows "(\<Sum> k < n. f k) = f 0 + (\<Sum> k \<in> {1..<n}. f k)"
  using assms
  by (simp add: atLeast1_lessThan_eq_remove0 sum.remove)

theorem IMO_2006_SL_A2:
  fixes a :: "nat \<Rightarrow> real"
  assumes "a 0 = -1" "\<forall> n \<ge> 1. (\<Sum> k < Suc n. a (n - k) / (k + 1)) = 0" "n \<ge> 1"
  shows "a n > 0"
  using \<open>n \<ge> 1\<close>
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof cases
    assume "n = 1"
    have "a 1 = 1/2"
      using assms
      by auto
    with \<open>n = 1\<close> show ?thesis 
      by simp
  next
    assume "n \<noteq> 1"
    with \<open>n \<ge> 1\<close> have "n > 1"
      by simp

    have "0 = (n + 1) * (\<Sum> k < n + 1. a k / (n + 1 - k)) - n * (\<Sum> k < n. a k / (n - k))"
    proof-
      have "(\<Sum> k < n. a k / (n - k)) = 0"
        using assms(2)[rule_format, of "n - 1"] \<open>n > 1\<close> 
              sum.nat_diff_reindex[of "\<lambda> k. a k / (n - k)" "n"]
        by simp

      moreover

      have "(\<Sum> k < n + 1. a k / (n + 1 - k)) = 0"
        using assms(2)[rule_format, of "n"] \<open>n > 1\<close>
              sum.nat_diff_reindex[of "\<lambda> k. a k / (n + 1 - k)" "n + 1"]
        by simp

      ultimately
      show ?thesis
        by simp
    qed
    then have "(n + 1) * a n = - (\<Sum> k < n. ((n + 1) / (n + 1 - k) - n / (n - k)) * a k)"
      by (simp add: algebra_simps sum_distrib_left sum_subtractf)
    then have "(n + 1) * a n = (\<Sum> k < n. (n / (n - k) - (n + 1) / (n + 1 - k)) * a k)"
      by (simp add: algebra_simps sum_negf[symmetric])
    also have "... = (\<Sum> k \<in> {1..<n}. (n / (n - k) - (n + 1) / (n + 1 - k)) * a k)"
      using \<open>n > 1\<close> 
      by (subst sum_remove_zero, auto)
    also have "... > 0"
    proof (rule sum_pos)
      show "finite {1..<n}"
        by simp
    next
      show "{1..<n} \<noteq> {}"
        using \<open>n > 1\<close>
        by simp
    next
      fix i
      assume "i \<in> {1..<n}"
      show "(n / (n - i) - (n + 1) / (n + 1 - i)) * a i > 0" (is "?c * a i > 0")
      proof-
        have "a i > 0" using less \<open>i \<in> {1..<n}\<close> by simp

        moreover have "?c > 0"
        proof-
          have "?c = i / ((n - i) * (n + 1 - i))"
            using \<open>i \<in> {1..<n}\<close>
            by (simp add: field_simps of_nat_diff)
          then show ?thesis
            using \<open>i \<in> {1..<n}\<close>
            by simp
        qed

        ultimately show ?thesis by simp
      qed
    qed
    finally have "(n + 1) * a n > 0"
      .
    then show ?thesis
      by (smt mult_nonneg_nonpos of_nat_0_le_iff)
  qed                             
qed

end