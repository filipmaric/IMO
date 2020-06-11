section \<open>Combinatorics problems\<close>

subsection \<open>IMO 2018 SL - C1\<close>

theory IMO_2018_SL_C1_sol
imports Complex_Main
begin

lemma sum_geom_nat:
  fixes q::nat
  assumes "q > 1"
  shows "(\<Sum>k\<in>{0..<n}. q^k) = (q^n - 1) div (q - 1)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (smt Nat.add_diff_assoc2 One_nat_def Suc_1 Suc_leI add.commute assms div_mult_self4 le_trans mult_eq_if nat_one_le_power one_le_numeral power.simps(2) sum.op_ivl_Suc zero_less_diff zero_order(3))
qed

declare [[smt_timeout = 20]]

lemma div_diff_nat:
  fixes a b c :: nat
  assumes "c dvd a" "c dvd b"
  shows "(a - b) div c = a div c  - b div c"
  using assms
  by (smt add_diff_cancel_left' div_add dvd_diff_nat le_iff_add nat_less_le neq0_conv not_less zero_less_diff) 

lemma sum_geom_nat':
  fixes q::nat
  assumes "q > 1" "m \<le> n"
  shows "(\<Sum>k\<in>{m..<n}. q^k) = (q^n - q^m) div (q - 1)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  show ?case
  proof (cases "m \<le> n")
    case True
    then have "sum ((^) q) {m..<Suc n} = (q ^ n - q ^ m) div (q - 1) + q^n"
      using Suc
      by simp
    also have "... = ((q ^ n - q ^ m) + (q - 1) * q^n) div (q - 1)"
      using \<open>q > 1\<close>
      by auto
    also have "... = ((q ^ n - q ^ m) + (q^(n+1) - q^n)) div (q - 1)"
      by (simp add: algebra_simps)
    also have "... = (q ^ (n+1) - q ^ m) div (q - 1)"
      using True assms(1) by auto
    finally show ?thesis
      by simp
  next
    case False
    then have "m = n + 1"
      using Suc(3)
      by auto
    then show ?thesis
      by simp
  qed
qed


theorem IMO2018SL_C1:
  fixes n :: nat
  assumes "n \<ge> 3"
  shows "\<exists> (S::nat set). card S = 2*n \<and> (\<forall> x \<in> S. x > 0) \<and> 
        (\<forall> m. 2 \<le> m \<and> m \<le> n \<longrightarrow> (\<exists> S1 S2. S1 \<inter> S2 = {} \<and> S1 \<union> S2 = S \<and> card S1 = m \<and> \<Sum> S1 = \<Sum> S2))"
proof-
  let ?Sa = "{(3::nat)^k | k. k \<in> {1..<n}}" and ?Sb = "{2 * (3::nat)^k | k. k \<in> {1..<n}}" and ?Sc = "{1::nat, (3^n + 9) div 2 - 1}"
  let ?S = "?Sa \<union> ?Sb \<union> ?Sc"

  have "finite ?Sa" "finite ?Sb" "finite ?Sc" "finite (?Sa \<union> ?Sb)"
    by auto

  have "?Sa \<inter> ?Sb = {}"
  proof safe
    fix ka kb
    assume "ka \<in> {1..<n}" "kb \<in> {1..<n}" "(3::nat)^ka = 2*3^kb"
    have "odd ((3::nat)^ka)" "even (2*3^kb)"
      by simp_all
    then have False
      using \<open>(3::nat)^ka = 2*3^kb\<close>
      by simp
    then show "3^ka \<in> {}"
      by simp
  qed

  have "1 < ((3::nat) ^ n + 9) div 2"
    by linarith

  have "\<not> 3 dvd (((3::nat) ^ n + 9) div 2 - 1)"
  proof-
    have "3 dvd ((3::nat) ^ n + 9) div 2"
    proof-
      have "(3::nat) ^ n + 9 = (3^2) * (3::nat)^(n-2) + 9"
        using \<open>n \<ge> 3\<close>
        by (metis One_nat_def add_leD2 le_add_diff_inverse numeral_3_eq_3 one_add_one plus_1_eq_Suc power_add)
      then have "(3::nat) ^ n + 9 = 9*(3^(n-2) + 1)"
        by simp
      then have "((3::nat) ^ n + 9) div 2 = (9 * (3^(n-2) + 1)) div 2"
        by auto
      then have "((3::nat) ^ n + 9) div 2 = 9 * ((3^(n-2) + 1) div 2)"
        by (metis One_nat_def div_mult_swap dvd_mult_div_cancel even_add even_power even_succ_div_two num.distinct(1) numeral_3_eq_3 numeral_eq_one_iff one_add_one plus_1_eq_Suc)
      then show ?thesis
        by simp
    qed
    then show ?thesis
      using \<open>((3::nat) ^ n + 9) div 2 > 1\<close>
      by (meson dvd_diffD1 less_imp_le_nat nat_dvd_1_iff_1 numeral_eq_one_iff semiring_norm(86))
  qed

  have "(?Sa \<union> ?Sb) \<inter> ?Sc = {}"
  proof-
    have "?Sa \<inter> ?Sc = {}"
    proof safe
      fix k
      assume "k \<in> {1..<n}" "(3::nat) ^ k = 1"
      then show "3 ^ k \<in> {}"
        by simp
    next
      fix k
      assume "k \<in> {1..<n}" "(3::nat) ^ k = (3 ^ n + 9) div 2 - 1"
      moreover
      have "3 dvd (3::nat) ^ k"
        using \<open>k \<in> {1..<n}\<close>
        by auto
      ultimately
      have False
        using \<open>\<not> 3 dvd (3 ^ n + 9) div 2 - 1\<close>
        by simp
      then show "3 ^ k \<in> {}"
        by simp
    qed

    moreover

    have "?Sb \<inter> ?Sc = {}"
    proof safe
      fix k
      assume "k \<in> {1..<n}" "2 * (3::nat) ^ k = 1"
      then show "2 * 3 ^ k \<in> {}"
        by simp
    next
      fix k
      assume "k \<in> {1..<n}" "2 * (3::nat) ^ k = (3 ^ n + 9) div 2 - 1"
      moreover
      have "3 dvd 2 * (3::nat) ^ k"
        using \<open>k \<in> {1..<n}\<close>
        by auto
      ultimately
      have False
        using \<open>\<not> 3 dvd (3 ^ n + 9) div 2 - 1\<close>
        by simp
      then show "2 * 3 ^ k \<in> {}"
        by simp
    qed

    ultimately
    show ?thesis
      by blast
  qed

  show ?thesis
  proof (rule_tac x="?S" in exI, safe)
    show "card ?S = 2*n"
    proof-
      have "card (?Sa \<union> ?Sb) = (n - 1) + (n - 1)"
      proof-
        have "inj_on ((^) (3::nat)) {1..<n}"
          unfolding inj_on_def
          by auto
        then have "card ?Sa = n-1"
          using card_image[of "\<lambda> k. 3^k" "{1..<n}"]
          by (smt Collect_cong Setcompr_eq_image card_atLeastLessThan)

        moreover

        have "inj_on (\<lambda> k. 2 * (3::nat) ^ k) {1..<n}"
          unfolding inj_on_def
          by auto
       
        then have "card ?Sb = n-1"
          using card_image[of "\<lambda> k. 2 * 3^k" "{1..<n}"]
          by (smt Collect_cong Setcompr_eq_image card_atLeastLessThan)


        ultimately
        show ?thesis
          using \<open>n \<ge> 3\<close> card_Un_disjoint[of ?Sa ?Sb] \<open>?Sa \<inter> ?Sb = {}\<close> \<open>finite ?Sa\<close> \<open>finite ?Sb\<close>
          by smt
      qed

      moreover

      have "card {1, ((3::nat)^n + 9) div 2 - 1} = 2"
        using \<open>1 < ((3::nat) ^ n + 9) div 2\<close>
        by auto

      ultimately

      show "card ?S = 2*n"
        using \<open>n \<ge> 3\<close> card_Un_disjoint[of "?Sa \<union> ?Sb" ?Sc] \<open>(?Sa \<union> ?Sb) \<inter> ?Sc = {}\<close> \<open>finite (?Sa \<union> ?Sb)\<close> \<open>finite ?Sc\<close>
        by (smt Nat.add_diff_assoc2 Suc_1 Suc_eq_plus1 add_Suc_right card_infinite diff_add_inverse2 le_trans mult_2 nat.simps(3) one_le_numeral)
    qed
  next
    fix k
    assume "k \<in> {1..<n}"
    then show "0 < (3::nat) ^ k" "0 < 2 * (3::nat) ^ k"
      by simp_all
  next
    show "0 < ((3::nat) ^ n + 9) div 2 - 1"
      using \<open>1 < (3 ^ n + 9) div 2\<close> zero_less_diff
      by blast
  next
    fix m
    assume "2 \<le> m" "m \<le> n"
    let ?Am' = "{2 * (3::nat)^k | k. k \<in> {n-m+1..<n}}" and ?Am'' = "{(3::nat) ^ (n-m+1)}"
    let ?Am = "?Am' \<union> ?Am''"
    let ?Bm = "?S - ?Am"

    have "?Am' \<subseteq> ?Sb"
      using \<open>m \<le> n\<close>
      by auto

    have "?Am'' \<subseteq> ?Sa"
      using \<open>m \<le> n\<close> \<open>2 \<le> m\<close>
      by force


    have "?Am \<inter> ?Bm = {}"
      by blast

    moreover

    have Am: "?Am' \<inter> ?Am'' = {}"  "finite ?Am'" "finite ?Am''"
      using \<open>?Am' \<subseteq> ?Sb\<close> \<open>?Am'' \<subseteq> ?Sa\<close> \<open>?Sa \<inter> ?Sb = {}\<close>
      by auto

    have "finite ?Am" "finite ?Bm"
      by auto

    have "?Am \<union> ?Bm = ?S"
    proof-
      have "?Am \<subseteq> ?S"
        using \<open>?Am' \<subseteq> ?Sb\<close> \<open>?Am'' \<subseteq> ?Sa\<close>
        by blast
      then show ?thesis
        by blast
    qed
                   
    moreover

    have "card ?Am = m"
    proof-
      have "inj_on (\<lambda> k. 2 * (3::nat) ^ k) {n-m+1..<n}"
        unfolding inj_on_def
        by auto
      then show ?thesis
        using card_image[of "\<lambda> k. 2 * (3::nat)^k" "{n-m+1..<n}"] 
              card_Un_disjoint[of ?Am' ?Am''] Am
        unfolding Setcompr_eq_image
        by (smt Int_insert_right_if1 One_nat_def Suc_eq_plus1 Un_insert_right \<open>({2 * 3 ^ k |k. k \<in> {n - m + 1..<n}} \<union> {3 ^ (n - m + 1)}) \<inter> ({3 ^ k |k. k \<in> {1..<n}} \<union> {2 * 3 ^ k |k. k \<in> {1..<n}} \<union> {1, (3 ^ n + 9) div 2 - 1} - ({2 * 3 ^ k |k. k \<in> {n - m + 1..<n}} \<union> {3 ^ (n - m + 1)})) = {}\<close> \<open>2 \<le> m\<close> \<open>m \<le> n\<close> add.commute add_diff_inverse_nat add_le_cancel_left card.insert card_atLeastLessThan card_empty diff_Suc_Suc diff_diff_cancel disjoint_insert(2) finite.emptyI insertCI insert_absorb le_trans linorder_not_le one_le_numeral)
    qed

    moreover
    have "\<Sum> ?Am = \<Sum> ?Bm"
    proof-
      have "(\<Sum> ?Am) = 3^n"
      proof-
        have "\<Sum> ?Am' = (\<Sum>k\<in>{n-m+1..<n}. 2*3^k)"
        proof-
          have "inj_on (\<lambda> k. 2*(3::nat)^k) {n-m+1..<n}"
            unfolding inj_on_def
            by auto
          then show ?thesis
            unfolding Setcompr_eq_image
            by (simp add: sum.reindex_cong)
        qed
        also have "... = 2 * (\<Sum>k\<in>{n-m+1..<n}. 3^k)"
          by (simp add: sum_distrib_left)
        also have "... = 3^n - 3^(n-m+1)"
          using sum_geom_nat'[of 3 "n-m+1" n] \<open>m \<ge> 2\<close> \<open>m \<le> n\<close>
          by simp
        finally
        have "\<Sum> ?Am' = 3^n - 3^(n-m+1)"
          .

        moreover

        have "\<Sum> ?Am'' = 3^(n-m+1)"
          by simp

        moreover

        have "\<Sum> ?Am = \<Sum> ?Am' + \<Sum> ?Am''"
          using Am
          by (simp add: sum.union_disjoint)

        ultimately

        have "(\<Sum> ?Am) = (3^n - 3^(n-m+1)) + 3^(n-m+1)"
          by simp
        also have "... = 3^n"
        proof-
          have "(3::nat)^(n-m+1) \<le> 3^n"
            using \<open>m \<le> n\<close> \<open>2 \<le> m\<close>
            by (metis Nat.le_diff_conv2 add.commute add_leD2 diff_diff_cancel diff_le_self one_le_numeral power_increasing)
          then show ?thesis
            by simp
        qed
        finally show ?thesis
          .
      qed

      moreover

      have "\<Sum> ?Bm = 3^n"
      proof-
        have "\<Sum> ?S = 2*3^n"
        proof-
          have "\<Sum> ?Sa = (\<Sum> k\<in>{1..<n}. 3^k)"
          proof-
            have "inj_on ((^) (3::nat)) {1..<n}"
              unfolding inj_on_def
              by auto
            then show ?thesis
              unfolding Setcompr_eq_image
              by (simp add: sum.reindex_cong)
          qed

          have "\<Sum> ?Sa = (3^n - 1) div 2 - 1"
          proof-
            have "inj_on (\<lambda> k. (3::nat) ^ k) {1..<n}"
              unfolding inj_on_def
              by auto
            then have "\<Sum> ?Sa = (\<Sum> k \<in> {1..<n}. 3 ^ k)"
              unfolding Setcompr_eq_image
              by (simp add: sum.reindex_cong)
            then show ?thesis
              using sum_geom_nat'[of 3 1 n] \<open>n \<ge> 3\<close>
              by simp
          qed

          moreover

          have "\<Sum> ?Sb = 2 * ((3^n - 1) div 2 - 1)"
          proof-
            have "inj_on (\<lambda> k. 2 * (3::nat) ^ k) {1..<n}"
              unfolding inj_on_def
              by auto
            then have "\<Sum> ?Sb = (\<Sum> k \<in> {1..<n}. 2 * 3 ^ k)"
              unfolding Setcompr_eq_image
              by (simp add: sum.reindex_cong)
            also have "... = 2 * (\<Sum> k \<in> {1..<n}. 3 ^ k)"
              by (simp add: sum_distrib_left)
            also have "... = 2 * (\<Sum> ?Sa)"
            proof-
              have "inj_on (\<lambda> k. (3::nat) ^ k) {1..<n}"
                unfolding inj_on_def
                by auto
              then show ?thesis
                unfolding Setcompr_eq_image
                by (simp add: sum.reindex_cong)
            qed
            finally 
            show ?thesis
              using \<open>\<Sum> ?Sa = (3^n - 1) div 2 - 1\<close>
              by simp
          qed

          moreover

          have "\<Sum> ?Sc = (3 ^ n + 9) div 2"
            by auto

          moreover

          have "\<Sum> ?S = \<Sum> ?Sa + \<Sum> ?Sb + \<Sum> ?Sc"
            using \<open>?Sa \<inter> ?Sb = {}\<close> \<open>(?Sa \<union> ?Sb) \<inter> ?Sc = {}\<close>
            using \<open>finite ?Sa\<close> \<open>finite ?Sb\<close> \<open>finite ?Sc\<close> \<open>finite (?Sa \<union> ?Sb)\<close>
            using sum.union_disjoint
            by (metis (no_types, lifting))

          moreover

          have "(((3::nat)^n - 1) div 2 - 1) + 2 * ((3^n - 1) div 2 - 1) + (3 ^ n + 9) div 2 = 2*3^n" (is "?lhs = 2*3^n")
          proof-
            have "((3::nat)^n - 1) div 2 - 1 = (3^n - 3) div 2"
              by simp
            then have "?lhs =  3*((3^n - 3) div 2) + (3 ^ n + 9) div 2"
              by simp
            also have "... = ((3*3^n - 9) + (3^n + 9)) div 2"
              by (simp add: div_mult_swap)
            also have "... = 2*3^n"
            proof-
              have "9 \<le> (3::nat) * 3 ^ n"
                using \<open>n \<ge> 3\<close>
                by (smt Suc_1 \<open>(3 ^ n - 1) div 2 - 1 = (3 ^ n - 3) div 2\<close> calculation diff_add_inverse2 diff_diff_cancel diff_is_0_eq dvd_mult_div_cancel even_add even_power le_add1 le_add_same_cancel2 le_antisym le_trans linear mult_Suc numeral_3_eq_3 odd_two_times_div_two_succ plus_1_eq_Suc power_mult self_le_ge2_pow)
              then have "((3::nat)*3^n - 9) + (3^n + 9) = 4*3^n"
                by simp
              then show ?thesis
                by simp
            qed
            finally
            show ?thesis
              .
          qed

          ultimately
          show ?thesis
            by simp
        qed
        also have "\<Sum> ?S = \<Sum> ?Am + \<Sum> ?Bm"
          using \<open>?Am \<union> ?Bm = ?S\<close> \<open>?Am \<inter> ?Bm = {}\<close> \<open>finite ?Am\<close> \<open>finite ?Bm\<close>
          using sum.union_disjoint[of ?Am ?Bm id]
          by simp
        then show ?thesis
          using \<open>\<Sum> ?Am = 3^n\<close>
          by (metis (no_types, lifting) add_left_cancel calculation mult_2)
      qed

      ultimately

      show ?thesis
        by simp
    qed

    ultimately

    show "\<exists>S1 S2. S1 \<inter> S2 = {} \<and> S1 \<union> S2 = ?S \<and> card S1 = m \<and> \<Sum> S1 = \<Sum> S2"
      by blast
  qed
qed

end