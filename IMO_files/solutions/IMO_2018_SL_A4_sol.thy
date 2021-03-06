subsection \<open>IMO 2018 SL - A4\<close>

theory IMO_2018_SL_A4_sol
imports Complex_Main
begin

definition is_Max :: "'a::linorder set \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_Max A x \<longleftrightarrow> x \<in> A \<and> (\<forall> x' \<in> A. x' \<le> x)"

lemma sum_list_cong:
  assumes "\<And> x. x \<in> set l \<Longrightarrow> f x = g x"
  shows "(\<Sum> x \<leftarrow> l. f x) = (\<Sum> x \<leftarrow> l. g x)"
  using assms
  by (metis map_eq_conv)

lemma Max_ge_Min:
  assumes "finite A" "A \<noteq> {}"
  shows "Max A \<ge> Min A"
  using assms
  by simp

theorem IMO2018SL_A4:
  shows
  "is_Max {a 2018 - a 2017 | a::nat \<Rightarrow> real. a 0 = 0 \<and> a 1 = 1 \<and> (\<forall> n \<ge> 2. \<exists> k. 1 \<le> k \<and> k \<le> n \<and> a n = (\<Sum> i \<leftarrow> [n-k..<n]. a i) / real k)}
   (2016 / 2017^2)" (is "is_Max {?f a | a. ?P a} ?m")
  unfolding is_Max_def
proof
  show "?m \<in> {?f a | a. ?P a}"
  proof-
    let ?a = "(\<lambda> n. if n = 0 then 0
                    else if n < 2017 then 1
                    else if n = 2017 then 1 - 1/2017
                    else 1 - 1/2017^2) :: (nat \<Rightarrow> real)"
    have "?P ?a"
    proof safe
      show "?a 0 = 0"
        by simp
    next
      show "?a 1 = 1"
        by simp
    next
      fix n::nat
      assume "2 \<le> n"
      
      show "\<exists> k. 1 \<le> k \<and> k \<le> n \<and> ?a n = (\<Sum>i\<leftarrow>[n - k..< n]. ?a i) / real k"
      proof (cases "n < 2017")
        case True
        have "[n-1..<n] = [n-1]"
          using \<open>n \<ge> 2\<close>
          by (simp add: upt_rec)
        then show ?thesis
          using \<open>n \<ge> 2\<close> \<open>n < 2017\<close>
          by (rule_tac x=1 in exI, auto)
      next
        case False
        show ?thesis
        proof (cases "n = 2017")
          case True
          have "[0..<2017] = [0] @ [1..<2017]"
            by (metis One_nat_def less_numeral_extra(4) numeral_eq_Suc plus_1_eq_Suc upt_add_eq_append upt_rec zero_le_one zero_less_one)
          then have "(\<Sum>i\<leftarrow>[0..<2017]. ?a i) = ?a 0 + (\<Sum>i\<leftarrow>[1..<2017]. ?a i)"
            by simp
          then have "(\<Sum>i\<leftarrow>[0..<2017]. ?a i) = (\<Sum>i\<leftarrow>[0..<1]. 0) + (\<Sum>i\<leftarrow>[1..<2017]. 1)"
            using sum_list_cong[of "[1..<2017]" ?a "\<lambda> k. 1"]
            by auto
          then have "(\<Sum>i\<leftarrow>[0..<2017]. ?a i) = 2016"
            by (simp add: sum_list_triv)
          then show ?thesis
            using \<open>n = 2017\<close>
            by (rule_tac x="2017" in exI, auto)
        next
          case False
          show ?thesis
          proof (cases "n = 2018")
            case True
            have "[1..<2018] = [1..<2017] @ [2017]"
              by (metis one_le_numeral one_plus_numeral plus_1_eq_Suc semiring_norm(4) semiring_norm(5) upt_Suc_append)
            then have "(\<Sum>i\<leftarrow>[1..<2018]. ?a i) = (\<Sum>i\<leftarrow>[1..<2017]. ?a i) + ?a 2017"
              using sum_list_append[of "[1..<2017]" "[2017..<2018]"]
              by simp
            then have "(\<Sum>i\<leftarrow>[1..<2018]. ?a i) = 2016 + (1 - 1/2017)"
              using sum_list_cong[of "[1..<2017]" ?a "\<lambda> k. 1"]
              by (simp add: sum_list_triv)
            then show ?thesis
              using \<open>n = 2018\<close>
              by (rule_tac x="2017" in exI, auto)
          next
            case False
            have "[n-1..<n] = [n-1]"
              using \<open>n \<ge> 2\<close>
              by (simp add: upt_rec)
            then show ?thesis
              using \<open>\<not> n < 2017\<close> \<open>n \<noteq> 2017\<close> \<open>n \<noteq> 2018\<close> \<open>n \<ge> 2\<close>
              by (rule_tac x=1 in exI, auto)
          qed
        qed
      qed
    qed
    moreover
    have "?f ?a = ?m"
      by simp
    ultimately
    show ?thesis
      by (smt mem_Collect_eq)
  qed
next
  show "\<forall> x' \<in> {?f a | a. ?P a}. x' \<le> ?m"
  proof safe
    fix a :: "nat \<Rightarrow> real"
    let ?S = "\<lambda> n k. (\<Sum> i \<leftarrow> [n-k..<n]. a i)"
    assume "a 0 = 0" "a 1 = 1" and *: " \<forall>n\<ge>2. \<exists>k\<ge>1. k \<le> n \<and> a n = ?S n k / real k"
    let ?A = "\<lambda> n. {?S n k / k | k. k \<in> {1..<n+1}}"
    let ?max = "\<lambda> n. Max (?A n)"
    let ?min = "\<lambda> n. Min (?A n)"
    let ?\<Delta> = "\<lambda> n. ?max n - ?min n"

    have A: "\<forall> n \<ge> 1. finite (?A n) \<and> ?A n \<noteq> {}"
      by auto

    have "\<forall> n \<ge> 2. ?\<Delta> n \<ge> 0"
    proof safe
      fix n::nat
      assume "2 \<le> n"
      then have "?max n \<ge> ?min n"
        using Max_ge_Min[of "?A n"] A[rule_format, of n]
        by force
      then show "?\<Delta> n \<ge> 0"
        by simp
    qed

    have "\<forall> n \<ge> 2. ?min n \<le> a n \<and> a n \<le> ?max n"
    proof safe
      fix n::nat
      assume "n \<ge> 2"
      then have "n \<ge> 1"
        by simp
      have "a n \<in> ?A n"
        using * \<open>n \<ge> 2\<close>
        by force
      then show "?min n \<le> a n" "a n \<le> ?max n"
        using A[rule_format, OF \<open>n \<ge> 1\<close>] 
        using Min_le[of "?A n" "a n"] Max_ge[of "?A n" "a n"]
        by blast+
    qed

    have "\<forall> n \<ge> 2. a (n - 1) \<in> ?A n"
    proof safe
      fix n::nat
      assume "n \<ge> 2"
      then have "[n-1..<n] = [n-1]"
        using upt_rec by auto
      then have "a (n - 1) = ?S n 1"
        by simp
      then show "\<exists> k. a (n - 1) = ?S n k / k \<and> k \<in> {1..<n+1}"
        using \<open>n \<ge> 2\<close>
        by force
    qed

    have "\<forall> n \<ge> 2. ?min n \<le> a (n-1) \<and> a (n-1) \<le> ?max n"
    proof safe
      fix n::nat
      assume "n \<ge> 2"
      then have "n \<ge> 1"
        by simp
      have "a (n - 1) \<in> ?A n"
        using \<open>\<forall> n \<ge> 2. a (n - 1) \<in> ?A n\<close> \<open>n \<ge> 2\<close>
        by force
      then show "?min n \<le> a (n - 1)" "a (n - 1) \<le> ?max n"
        using A[rule_format, OF \<open>n \<ge> 1\<close>] 
        using Min_le[of "?A n" "a (n - 1)"] Max_ge[of "?A n" "a (n - 1)"]
        by blast+
    qed

    have "?f a \<le> ?\<Delta> 2018"
      using \<open>\<forall> n \<ge> 2. ?min n \<le> a n \<and> a n \<le> ?max n\<close>[rule_format, of 2018]
      using \<open>\<forall> n \<ge> 2. ?min n \<le> a (n-1) \<and> a (n-1) \<le> ?max n\<close>[rule_format, of 2018]
      by auto

    have Claim1: "\<forall> n > 2. ?\<Delta> n \<le> (n-1)/n * ?\<Delta> (n-1)"
    proof safe
      fix n::nat
      assume "2 < n"
      then have "1 \<le> n"
        by simp
      obtain k where "?max n = ?S n k / k" "1 \<le> k" "k \<le> n"
        using A[rule_format, OF \<open>1 \<le> n\<close>] Max_in[of "?A n"]
        by force
      obtain l where "?min n = ?S n l / l" "1 \<le> l" "l \<le> n"
        using A[rule_format, OF \<open>1 \<le> n\<close>] Min_in[of "?A n"]
        by force

      have "[n - k..<n] = [n - 1 - (k - 1)..<n - 1] @ [n - 1]"
        using  \<open>1 \<le> k\<close> \<open>k \<le> n\<close> \<open>1 \<le> n\<close>
        by (metis Nat.diff_diff_eq diff_le_self le_add_diff_inverse plus_1_eq_Suc upt_Suc_append)
      then have "?S n k = ?S (n-1) (k-1) + a (n-1)"
        by simp

      have "[n - l..<n] = [n - 1 - (l - 1)..<n - 1] @ [n - 1]"
        using \<open>1 \<le> l\<close> \<open>l \<le> n\<close> \<open>1 \<le> n\<close>
        by (metis Nat.diff_diff_eq diff_le_self le_add_diff_inverse plus_1_eq_Suc upt_Suc_append)
      then have "?S n l = ?S (n-1) (l-1) + a (n-1)"
        by simp

      have "real (k - Suc 0) = real k - 1"
        using \<open>k \<ge> 1\<close>
        by simp

      have "?S (n-1) (k-1) \<le> (k - 1) * ?max (n - 1)"
      proof (cases "k = 1")
        case True
        then show ?thesis
          by simp
      next
        case False
        have "n-1 \<ge> 1"
          using \<open>n > 2\<close>
          by simp
        have "?S (n-1) (k-1) / (k - 1) \<le> ?max (n - 1)"
        proof (rule Max_ge)
          show "finite (?A (n-1))"
            using A[rule_format, OF \<open>n-1 \<ge> 1\<close>]
            by simp
        next
          show "?S (n-1) (k-1) / (k - 1) \<in> ?A (n-1)"
            using \<open>k \<noteq> 1\<close> \<open>k \<ge> 1\<close> \<open>k \<le> n\<close>
            by simp (rule_tac x="k-1" in exI, auto)
        qed
        then show ?thesis
          using \<open>k \<ge> 1\<close> \<open>k \<noteq> 1\<close>
          by (simp add: field_simps)
      qed

      have "?S (n-1) (l-1) \<ge> (l - 1) * ?min (n - 1)"
      proof (cases "l = 1")
        case True
        then show ?thesis
          by simp
      next
        case False
        have "n-1 \<ge> 1"
          using \<open>n > 2\<close>
          by simp
        have "?S (n-1) (l-1) / (l - 1) \<ge> ?min (n - 1)"
        proof (rule Min_le)
          show "finite (?A (n-1))"
            using A[rule_format, OF \<open>n-1 \<ge> 1\<close>]
            by simp
        next
          show "?S (n-1) (l-1) / (l - 1) \<in> ?A (n-1)"
            using \<open>l \<noteq> 1\<close> \<open>l \<ge> 1\<close> \<open>l \<le> n\<close>
            by simp (rule_tac x="l-1" in exI, auto)
        qed
        then show ?thesis
          using \<open>l \<ge> 1\<close> \<open>l \<noteq> 1\<close>
          by (simp add: field_simps)
      qed

      have "?min (n-1) \<le> a (n-1)" "a (n-1) \<le> ?max (n-1)"
        using \<open>\<forall> n \<ge> 2. ?min n \<le> a n \<and> a n \<le> ?max n\<close>[rule_format, of "n-1"] \<open>n > 2\<close>
        by simp_all

      {
        fix x1 x2::real
        assume "0 < x1" "x1 \<le> x2"
        then have "(x1 - 1) / x1 \<le> (x2 - 1) / x2"
          by (metis (no_types, hide_lams) diff_divide_distrib diff_mono divide_self_if frac_le leD order_refl zero_le_one)          
      } note mono = this


      have "k*(?max n - a (n-1)) = ?S n k - k * a (n-1)"
        using \<open>?max n = ?S n k / k\<close>
        by (simp add: algebra_simps)
      also have "... = ?S (n-1) (k-1) - (real k - 1) * a (n-1)"
        using \<open>?S n k = ?S (n-1) (k-1) + a (n-1)\<close>
        by (simp add: field_simps)
      also have "... \<le> (k - 1) * ?max (n - 1) - (real k - 1) * a (n-1)"
        using \<open>?S (n-1) (k-1) \<le> (k - 1) * ?max (n - 1)\<close>
        by simp
      also have "... = (real k - 1) * (?max (n - 1) - a (n-1))"
        using \<open>k \<ge> 1\<close>
        by (auto simp add: right_diff_distrib)
      finally have "k*(?max n - a (n-1)) \<le> (real k - 1) * (?max (n - 1) - a (n-1))"
        .
      then have "?max n - a (n-1) \<le> (real k - 1) / k * (?max (n-1) - a (n-1))"
        using \<open>k \<ge> 1\<close>
        by (simp add: field_simps)
      also have "(real k - 1) / k * (?max (n-1) - a (n-1)) \<le> 
                 (real n - 1) / n * (?max (n-1) - a (n-1))"
      proof-
        have "(real k - 1) / k \<le> (real n - 1) / n"
          using mono[of "real k" "real n"] \<open>k \<le> n\<close> \<open>k \<ge> 1\<close>
          by simp
        then show ?thesis
          using \<open>a (n - 1) \<le> ?max (n-1)\<close>
          by (smt mult_cancel_right real_mult_le_cancel_iff1)
      qed
      finally
      have 1: "?max n - a (n-1) \<le> (real n - 1) / n * (?max (n-1) - a (n-1))"
        .

      have "l * (a (n-1) - ?min n) = l * a (n-1) - ?S n l"
        using \<open>?min n = ?S n l / l\<close>
        by (simp add: algebra_simps) 
      also have "... = (real l - 1) * a (n-1) - ?S (n-1) (l-1)"
        using \<open>?S n l = ?S (n-1) (l-1) + a (n-1)\<close>
        by (simp add: field_simps)
      also have "... \<le> (real l - 1) * a (n-1) - (l - 1) * ?min (n - 1)"
        using \<open>?S (n-1) (l-1) \<ge> (l - 1) * ?min (n - 1)\<close>
        by (simp add: field_simps)
      also have "... = (real l - 1) * (a (n-1) - ?min (n - 1))"
        using \<open>l \<ge> 1\<close>
        by (auto simp add: right_diff_distrib)
      finally have "l*(a (n-1) - ?min n) \<le> (real l - 1) * (a (n-1) - ?min (n - 1))"
        .
      then have "a (n-1) - ?min n \<le> (real l - 1) / l * (a (n-1) - ?min (n-1))"
        using \<open>l \<ge> 1\<close>
        by (simp add: field_simps)
      also have "(real l - 1) / l * (a (n-1) - ?min (n-1)) \<le> 
                 (real n - 1) / n * (a (n-1) - ?min (n-1))"
      proof-
        have "(real l - 1) / l \<le> (real n - 1) / n"
          using mono[of "real l" "real n"] \<open>l \<le> n\<close> \<open>l \<ge> 1\<close>
          by simp
        then show ?thesis
          using \<open>a (n - 1) \<ge> ?min (n-1)\<close>
          by (smt mult_cancel_right real_mult_le_cancel_iff1)
      qed
      finally
      have 2: "a (n-1) - ?min n \<le> (real n - 1) / n * (a (n-1) - ?min (n-1))"
        .

      have "?\<Delta> n = (?max n - a (n-1)) + (a (n-1) - ?min n)"
        by simp
      also have "... \<le> (real n - 1) / n * ((?max (n-1) - a (n-1)) + (a (n-1) - ?min (n-1)))"
        using 1 2
        by (simp add: right_diff_distrib')
      finally show "?\<Delta> n \<le> (real n - 1) / n * ?\<Delta> (n-1)"
        by simp
    qed

    obtain \<Delta> where "\<Delta> = ?\<Delta>" by auto
    then have Claim1': "\<forall> n > 2. \<Delta> n \<le> (n-1)/n * \<Delta> (n-1)"
      using Claim1
      by blast
    
    have Claim1_iter': "\<And> N q. \<lbrakk>2 \<le> q; q \<le> N\<rbrakk> \<Longrightarrow> \<Delta> (N+1) \<le> \<Delta> (q+1) * (q + 1) / (N + 1)"
    proof-
      fix N q :: nat
      assume "2 \<le> q" "q \<le> N"
      then show "\<Delta> (N+1) \<le> \<Delta> (q+1) * (q + 1) / (N + 1)"
      proof (induction N)
        case 0
        then show ?case
          by simp
      next
        case (Suc N)
        show ?case
        proof (cases "q \<le> N")
          case True
          have "\<Delta> (N + 2) \<le> ((N + 1)/(N + 2)) * \<Delta> (N + 1)"
            using Claim1'[rule_format, of "Suc N + 1"] \<open>2 \<le> q\<close> \<open>q \<le> N\<close>
            by simp
          moreover
          have "\<Delta> (N + 1) \<le> \<Delta> (q + 1) * (q + 1) / (N + 1)"
            using True \<open>2 \<le> q\<close> Suc(1)
            by simp
          then have "((N + 1)/(N + 2)) * \<Delta> (N + 1) \<le> ((N + 1)/(N + 2)) * (\<Delta> (q + 1) * (q + 1) / (N + 1))"
            by (subst real_mult_le_cancel_iff2, simp_all)
          ultimately
          show ?thesis
            by simp
        next
          case False
          then have "q = N+1"
            using Suc(3)
            by simp
          then show ?thesis
            by simp
        qed
      qed
    qed

    {
      fix q::nat
      assume "\<forall> n. 1 \<le> n \<and> n < q \<longrightarrow> a n = 1"

      have "\<forall> k. 1 \<le> k \<and> k < q \<longrightarrow> ?S q k = k"
      proof safe
        fix k::nat
        assume "1 \<le> k" "k < q"
        then have "(\<Sum> i \<leftarrow> [q-k..<q]. a i) = (\<Sum> i \<leftarrow> [q-k..<q]. 1)"
          using sum_list_cong[of "[q-k..<q]" a "\<lambda> i. 1"]
          using \<open>\<forall> n. 1 \<le> n \<and> n < q \<longrightarrow> a n = 1\<close> \<open>k < q\<close>
          by fastforce
        then show "?S q k = k"
          using \<open>1 \<le> k\<close> \<open>k < q\<close>
          by (simp add: sum_list_triv)
      qed
    }
    note all_1_Sqk = this

    {
      fix q::nat
      assume "q \<ge> 2"
      assume "\<forall> n. 1 \<le> n \<and> n < q \<longrightarrow> a n = 1"
      have "?S q q = q - 1"
      proof-
        have "[q-q..<q] = [0] @ [1..<q]"
          using \<open>2 \<le> q\<close>
          using upt_rec by auto
        then have "?S q q = (\<Sum> i \<leftarrow> [1..<q]. a i)"
          using \<open>a 0 = 0\<close>
          by auto
        also have "... = (\<Sum> i \<leftarrow> [1..<q]. 1::real)"
          using sum_list_cong[of "[1..<q]" a "\<lambda> i. 1"]
          using \<open>\<forall> n. 1 \<le> n \<and> n < q \<longrightarrow> a n = 1\<close>
          by simp
        finally show ?thesis
          by (simp add: sum_list_triv)
      qed
    } note all_1_Sqq = this

    show "?f a \<le> ?m"
    proof (cases "\<forall> n. 2 \<le> n \<and> n \<le> 2017 \<longrightarrow> a n = 1")
      case True
      then have "\<forall>n. 1 \<le> n \<and> n < 2018 \<longrightarrow> a n = 1"
        using \<open>a 1 = 1\<close>
        by (metis Suc_leI add_le_cancel_left le_eq_less_or_eq one_add_one one_plus_numeral plus_1_eq_Suc semiring_norm(4) semiring_norm(5))
      then have "\<forall> k. 1 \<le> k \<and> k \<le> 2018 \<longrightarrow> ?S 2018 k \<le> k"
        using all_1_Sqk[of 2018] all_1_Sqq[of 2018]
        by (smt Suc_leI le_eq_less_or_eq of_nat_1 of_nat_diff one_add_one one_less_numeral_iff plus_1_eq_Suc semiring_norm(76))
      then have "a 2018 \<le> 1"
        using *[rule_format, of 2018]
        by auto
      then show ?thesis
        using True
        by auto
    next
      case False
      let ?Q = "{q. 2 \<le> q \<and> q \<le> 2017 \<and> a q \<noteq> 1}"
      let ?q = "Min ?Q"
      have "?Q \<noteq> {}"
        using False \<open>a 1 = 1\<close>
        by auto
      then have "2 \<le> ?q" "?q \<le> 2017" "a ?q \<noteq> 1"
        using Min_in[of ?Q]
        by auto

      have "\<forall> n. 2 \<le> n \<and> n < ?q \<longrightarrow> a n = 1"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain n where "2 \<le> n" "n < ?q" "a n \<noteq> 1"
          by auto
        then have "n \<in> ?Q"
          using \<open>?q \<le> 2017\<close>
          by auto
        then show False
          using Min_le[of ?Q n] \<open>?Q \<noteq> {}\<close> \<open>a n \<noteq> 1\<close> \<open>n < ?q\<close>
          by auto
      qed

      obtain q where "q = ?q" "2 \<le> q" "q \<le> 2017" using \<open>2 \<le> ?q\<close> \<open>?q \<le> 2017\<close> by auto
      then have "\<forall> n. 1 \<le> n \<and> n < q \<longrightarrow> a n = 1"
        using \<open>\<forall> n. 2 \<le> n \<and> n < ?q \<longrightarrow> a n = 1\<close> \<open>a 1 = 1\<close>
        by (metis Suc_1 Suc_leI le_eq_less_or_eq)
      then have "\<forall> k. 1 \<le> k \<and> k < q \<longrightarrow> ?S q k = k"  "?S q q = q - 1"
        using all_1_Sqk[of q] all_1_Sqq[of q] \<open>2 \<le> q\<close>
        by simp_all
      then have "\<forall> k. 1 \<le> k \<and> k \<le> q \<longrightarrow> ?S q k \<le> k"
        using le_eq_less_or_eq
        by auto
      then have "a q \<le> 1"
        using *[rule_format, OF \<open>2 \<le> q\<close>]
        by auto
      then have "a q < 1"
        using \<open>q = ?q\<close> \<open>a ?q \<noteq> 1\<close>
        by auto

      have "a q = ?S q q / q"
        using *[rule_format, OF \<open>2 \<le> q\<close>] \<open>a q < 1\<close> \<open>\<forall> k. 1 \<le> k \<and> k < q \<longrightarrow> ?S q k = k\<close>
        by (metis div_by_1 less_le of_nat_1 of_nat_le_iff one_eq_divide_iff order_class.order.antisym zero_le_one)

      then have "a q = 1 - 1/q"
        using \<open>?S q q = q - 1\<close>
        using \<open>q \<ge> 2\<close>
        by (simp add: field_simps)

      have "\<forall> i. 1 \<le> i \<and> i \<le> q \<longrightarrow> ?S (q+1) i = i - 1/q"
      proof safe
        fix i
        assume "1 \<le> i" "i \<le> q"
        show "?S (q+1) i = i - 1/q"
        proof (cases "i = 1")
          case True
          then show ?thesis
            using \<open>a q = 1 - 1/q\<close>
            by simp
        next
          case False
          then have "?S (q+1) i = a q + ?S q (i-1)"
            using \<open>1 \<le> i\<close> \<open>i \<le> q\<close>
            by auto
          moreover
          have "?S q (i-1) = (i-1)"
            using \<open>\<forall> k. 1 \<le> k \<and> k < q \<longrightarrow> ?S q k = k\<close>[rule_format, of "i-1"]
            using \<open>1 \<le> i\<close> \<open>i \<le> q\<close> \<open>i \<noteq> 1\<close>
            using Suc_le_eq
            by auto
          ultimately
          show ?thesis
            using \<open>a q = 1 - 1/q\<close> \<open>1 \<le> i\<close>
            by simp
        qed
      qed

      have "?S (q+1) (q+1) = q - 1/q"
      proof-
        have "?S (q+1) (q+1) = a q + ?S q q"
          by simp
        then show ?thesis
          using \<open>?S q q = q - 1\<close> \<open>a q = 1 - 1/q\<close>
          using \<open>2 \<le> q\<close>
          by simp
      qed

      have qq: "(real q - 1 / real q) / (real q + 1) = (real q - 1) / real q"
      proof-
        have "(real q + 1) * ((real q - 1 / real q) / (real q + 1)) = (real q + 1) * ((real q - 1) / real q)"
          using \<open>2 \<le> q\<close>
          by simp (simp add: field_simps)
        then show ?thesis
          by (subst (asm) mult_left_cancel, simp_all)
      qed

      have "?min (q+1) = (real q - 1)/real q"  (is "?lhs = ?mn")
      proof (subst Min_eq_iff)
        show "finite (?A (q+1))"
          by simp
      next
        show "?A (q+1) \<noteq> {}"
          using \<open>q \<ge> 2\<close>
          by auto
      next
        show "?mn \<in> ?A (q+1) \<and> (\<forall> m' \<in> ?A (q+1). m' \<ge> ?mn)"
        proof
          have "?mn = 1 - 1/q"
            using \<open>2 \<le> q\<close>
            by (simp add: field_simps)
          then have "?mn = ?S (q+1) 1"
            using \<open>\<forall> i. 1 \<le> i \<and> i \<le> q \<longrightarrow> ?S (q+1) i = i - 1/q\<close>[rule_format, of 1] \<open>2 \<le> q\<close>
            by simp
          then show "?mn \<in> ?A (q+1)"
            by force
          show "\<forall> m' \<in> ?A (q+1). m' \<ge> ?mn"
          proof
            fix m'
            assume "m' \<in> ?A (q+1)"
            then obtain k where "k \<in> {1..<q+1+1}" "m' = ?S (q+1) k / k"
              by force
            show "m' \<ge> ?mn"
            proof (cases "k \<le> q")
              case True
              then have "m' = (k - 1/q) / k"
                using \<open>k \<in> {1..<q+1+1}\<close> \<open>m' = ?S (q+1) k / k\<close> 
                using \<open>\<forall> i. 1 \<le> i \<and> i \<le> q \<longrightarrow> ?S (q+1) i = i - 1/q\<close>
                by auto
              then have "m' = 1 - 1/(q*k)"
                using \<open>k \<in> {1..<q+1+1}\<close> \<open>q \<ge> 2\<close>
                by (simp add: field_simps)
              then show ?thesis
                using \<open>?mn = 1 - 1/q\<close> \<open>k \<in> {1..<q+1+1}\<close> \<open>2 \<le> q\<close>
                by simp (simp add: field_simps)
            next
              case False
              then have "k = q+1"
                using \<open>k \<in> {1..<q+1+1}\<close>
                by simp
              then have "m' = (real q - 1) / real q"
                using \<open>m' = ?S (q+1) k / k\<close> \<open>?S (q+1) (q+1) = q - 1/q\<close>
                using qq
                by (metis of_nat_1 of_nat_add)
              then show ?thesis
                by simp
            qed
          qed
        qed
      qed

      moreover

      have "?max (q+1) = ((real q)^2 - 1)/(real q)^2" (is "?lhs = ?mx")
      proof (subst Max_eq_iff)
        show "finite (?A (q+1))"
          by simp
      next
        show "?A (q+1) \<noteq> {}"
          using \<open>q \<ge> 2\<close>
          by auto
      next
        show "?mx \<in> ?A (q+1) \<and> (\<forall> m' \<in> ?A (q+1). m' \<le> ?mx)"
        proof
          have "?mx = (?S (q+1) q) / q"
            using \<open>\<forall> i. 1 \<le> i \<and> i \<le> q \<longrightarrow> ?S (q+1) i = i - 1/q\<close>[rule_format, of q] \<open>2 \<le> q\<close>
            by simp (simp add: field_simps power2_eq_square)
          moreover
          have "q \<in> {1..<q + 1 + 1}"
            using \<open>q \<ge> 2\<close>
            by simp
          ultimately
          show "?mx \<in> ?A (q+1)"
            by force

          show "\<forall> m' \<in> ?A (q+1). m' \<le> ?mx"
          proof 
            fix m'
            assume "m' \<in> ?A (q+1)"
            then obtain k where "k \<in> {1..<q+1+1}" "m' = ?S (q+1) k / k"
              by force
            show "m' \<le> ?mx"
            proof (cases "k \<le> q")
              case True
              then have "m' = (k - 1/q) / k"
                using \<open>k \<in> {1..<q+1+1}\<close> \<open>m' = ?S (q+1) k / k\<close> 
                using \<open>\<forall> i. 1 \<le> i \<and> i \<le> q \<longrightarrow> ?S (q+1) i = i - 1/q\<close>
                by auto
              then have "m' = 1 - 1/(q*k)"
                using \<open>k \<in> {1..<q+1+1}\<close> \<open>q \<ge> 2\<close>
                by (simp add: field_simps)
              moreover
              have "?mx = 1 - 1/(q*q)"
                using \<open>q \<ge> 2\<close>
                by (simp add: field_simps power2_eq_square)
              ultimately
              show ?thesis
                using \<open>k \<le> q\<close> \<open>2 \<le> q\<close> \<open>k \<in> {1..<q+1+1}\<close>
                by simp (simp add: field_simps)
            next
              case False
              then have "k = q+1"
                using \<open>k \<in> {1..<q+1+1}\<close>
                by simp
              then have "m' = (real q - 1) / real q"
                using \<open>m' = ?S (q+1) k / k\<close> \<open>?S (q+1) (q+1) = q - 1/q\<close> qq
                by (metis of_nat_1 of_nat_add)
              moreover
              have "q \<le> q^2"
                by (simp add: \<open>2 \<le> q\<close> power2_nat_le_imp_le)
              ultimately
              show ?thesis
                using \<open>2 \<le> q\<close>
                by simp (simp add: field_simps)
            qed
          qed
        qed
      qed
                
      ultimately

      have "?\<Delta> (q+1) = ((real q)^2 - 1)/(real q)^2 - (real q - 1)/real q"
        by simp
      also have "... = (real q - 1)/(real q)^2"
        using \<open>q \<ge> 2\<close>
        by (simp add: power2_eq_square field_simps)
      finally have del: "\<Delta> (q+1) = (real q - 1)/(real q)^2"
        using \<open>\<Delta> = ?\<Delta>\<close>
        by simp
      then have "\<Delta> (2017 + 1) \<le> (real q - 1) / (real q)\<^sup>2 * real (q + 1) / 2018"
        using Claim1_iter'[OF \<open>2 \<le> q\<close> \<open>q \<le> 2017\<close>]
        by simp
      also have "... = ((real q^2 - 1) / (real q)\<^sup>2) / 2018"
        by (simp add: field_simps power2_eq_square)
      also have "... = (1 - (1 / (real q)\<^sup>2)) / 2018"
        using \<open>q \<ge> 2\<close>
        by (simp add: field_simps)
      also have "... \<le> (1 - (1 / 2017^2)) / 2018"
      proof-
        have "q^2 \<le> 2017^2"
          using \<open>2 \<le> q\<close> \<open>q \<le> 2017\<close>
          using power_mono by blast
        then have "(real q)^2 \<le> 2017^2"
          by (metis of_nat_le_iff of_nat_numeral of_nat_power)
        then show ?thesis
          using \<open>2 \<le> q\<close>
          by (simp add: field_simps power2_eq_square)
      qed
      finally have "\<Delta> 2018 \<le> ?m"
        by simp

      then show ?thesis
        using \<open>?f a \<le> ?\<Delta> 2018\<close> \<open>\<Delta> = ?\<Delta>\<close>
        by simp
    qed
  qed
qed

end