section\<open>Algebra problems\<close>

subsection \<open>IMO 2006 SL - A2\<close>

theory IMO_2006_SL_A2
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
  using `n \<ge> 1`
proof (induct n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n = 1")
    case True
    hence "a 1 = 1/2"
      using assms(1) assms(2)[rule_format, of n]
      by simp
    thus ?thesis
      using `n = 1`
      by simp
  next
    case False
    hence "n > 1"
      using `n \<ge> 1`
      by simp
    hence "n - 1 \<ge> 1"
      by simp
    have "(\<Sum> k < n. a k / (n - k)) = 0" (is "?S1 = 0")
      using assms(2)[rule_format, of "n - 1"] `n > 1` `n - 1 \<ge> 1` 
      using sum.nat_diff_reindex[of "\<lambda> k. a k / (n - k)" "n"]
      by simp

    moreover

    have "(\<Sum> k < Suc n. a k / (n + 1 - k)) = 0" (is "?S2 = 0")
      using assms(2)[rule_format, of "n"] `n > 1`
      using sum.nat_diff_reindex[of "\<lambda> k. a k / (n + 1 - k)" "Suc n"]
      by auto

    ultimately
    have "(n + 1)*?S2 - n*?S1 = 0"
      by simp
    hence "(n + 1) * (a n + (\<Sum> k < n. a k / (n + 1 - k))) = n * ?S1"
      by (simp add: add.commute)
    hence "(n + 1) * a n = n * (\<Sum> k < n. a k / (n - k)) - (n + 1) * (\<Sum> k < n. a k / (n + 1 - k))"
      by (simp add: algebra_simps)
    also have "... = (\<Sum> k < n. n * a k / (n - k)) - (\<Sum> k < n. (n + 1) * a k / (n + 1 - k))"
      apply (subst sum_distrib_left)
      apply (subst sum_distrib_left)
      by simp
    also have "... = (\<Sum> k < n. n * a k / (n - k) - (n + 1) * a k / (n + 1 - k))"
      apply (subst sum_subtractf)
      by simp
    also have "... = (\<Sum> k < n. a k * (n / (n - k) - (n + 1) / (n + 1 - k)))"
      by (simp add: algebra_simps)
    also have "... = (\<Sum> k \<in> {1..<n}. a k * (n / (n - k) - (n + 1) / (n + 1 - k)))"
      using `n > 1`
      apply (subst sum_remove_zero[of "n"])
      by auto
    also have "... > 0"
    proof (rule sum_pos)
      show "finite {1..<n}"
        by simp
    next
      show "{1..<n} \<noteq> {}"
        using `n > 1`
        by simp
    next
      fix i
      assume "i \<in> {1..<n}"
      hence *: "1 \<le> i" "i < n"
        by auto
      hence "(n / (n - i) - (n + 1) / (n + 1 - i)) > 0"
      proof-
        let ?n = "real n" and ?i = "real i"
        have "(?n / (?n - ?i) - (?n + 1) / (?n + 1 - ?i)) > 0"
        proof-
          have "?n / (?n - ?i) - (?n + 1) / (?n + 1 - ?i) = ?i / ((?n - ?i) * (?n + 1 - ?i))"
            using *
            by (simp add: field_simps)
          thus ?thesis
            using *
            by simp
        qed
        thus ?thesis
          using *
          by (simp add: add.commute of_nat_diff)
      qed
      moreover
      have "a i > 0"
        using less(1)[of i] `1 \<le> i` `i < n`
        by simp
      ultimately
      show "a i * (n / (n - i) - (n + 1) / (n + 1 - i)) > 0"
        by simp
    qed
    ultimately
    have "(n + 1) * a n > 0"
      by simp
    thus ?thesis
      by (smt mult_nonneg_nonpos of_nat_0_le_iff)
  qed                                      
qed


end