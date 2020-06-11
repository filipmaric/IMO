section \<open>Algebra problems\<close>

subsection \<open>IMO 2018 SL - A2\<close>

theory IMO_2018_SL_A2_sol
imports Complex_Main
begin

lemma n_plus_1_mod_n:
  fixes n :: nat
  assumes "n > 1"
  shows "(n + 1) mod n = 1"
  by (metis assms mod_add_self1 mod_less)

lemma n_plus_2_mod_n:
  fixes n :: nat
  assumes "n > 2"
  shows "(n + 2) mod n = 2"
  by (metis assms mod_add_self1 mod_less)

theorem IMO2018SL_A2:
  fixes n :: nat
  assumes "n \<ge> 3"
  shows "(\<exists> a :: nat \<Rightarrow> real. a n = a 0 \<and> a (n+1) = a 1 \<and> 
                             (\<forall> i < n. (a i) * (a (i+1)) + 1 = a (i+2))) \<longleftrightarrow> 
         3 dvd n" (is "(\<exists> a. ?p1 a \<and> ?p2 a \<and> ?eq a) \<longleftrightarrow> 3 dvd n")
proof
  assume "3 dvd n"

  let ?a = "(\<lambda> n. if n mod 3 = 0 then 2 else -1) :: nat \<Rightarrow> real"
  show "\<exists> a. ?p1 a \<and> ?p2 a \<and> ?eq a"
  proof (rule_tac x="?a" in exI, safe)
    show "?p1 ?a"
      using \<open>3 dvd n\<close>
      by auto
  next
    show "?p2 ?a"
      using \<open>3 dvd n\<close>
      by auto
  next
    fix i
    assume "i < n"
    show "(?a i) * (?a (i+1)) + 1 = ?a (i+2)"
      by auto presburger+
  qed
next
  assume "\<exists> a. ?p1 a \<and> ?p2 a \<and> ?eq a"
  then obtain a where "?p1 a" "?p2 a" "?eq a"
    by auto


  let ?a = "\<lambda> i. a (i mod n)"
  have "?p1 ?a" "?p2 ?a"
    using \<open>?p1 a\<close> \<open>n \<ge> 3\<close> n_plus_1_mod_n n_plus_2_mod_n
    by auto

  have eq: "\<forall>i. ?a i * ?a (i + 1) + 1 = ?a (i + 2)"
  proof safe
    fix i
    have "a ((i + 1) mod n) = a (i mod n + 1)"
      using \<open>?p1 a\<close>
      by (simp add: mod_Suc)

    moreover

    have "a ((i + 2) mod n) = a (i mod n + 2)"
      using \<open>?p1 a\<close> \<open>?p2 a\<close>
      by (metis One_nat_def Suc_eq_plus1 add_Suc_right mod_Suc one_add_one)

    ultimately

    show "a (i mod n) * a ((i + 1) mod n) + 1 = a ((i + 2) mod n)"
      using \<open>?eq a\<close>
      using assms
      by auto
  qed

  have *: "\<forall> i. ?a i > 0 \<and> ?a (i + 1) > 0 \<longrightarrow> ?a (i + 2) > 1"
    using eq
    by (smt mult_pos_pos)

  have no_pos_pos: "\<forall> i. \<not> (?a i > 0 \<and> ?a (i + 1) > 0)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain i where "?a i > 0" "?a (i + 1) > 0"
      by auto

    have "\<forall> j \<ge> i+1. ?a j > 0 \<and> ?a (j + 1) > 1"
    proof (rule allI, rule impI)
      fix j
      assume "i + 1 \<le> j"
      then show "0 < ?a j \<and> 1 < ?a (j + 1)"
      proof (induction j)
        case 0
        then show ?case
          by simp
      next
        case (Suc j)
        show ?case
        proof (cases "i + 1 \<le> j")
          case False
          then have "i + 1 = Suc j"
            using Suc(2)
            by auto
          then show ?thesis
            using \<open>?a i > 0\<close> \<open>?a (i + 1) > 0\<close> *
            by auto
        next
          case True
          then show ?thesis
            using Suc(1) *
            by (smt Suc_eq_plus1 add_Suc_right one_add_one)
        qed
      qed
    qed

    then have "\<forall> j \<ge> i+2. ?a j > 1"
      by (metis Suc_eq_plus1 add_Suc_right le_iff_add one_add_one plus_nat.simps(2))

    have *: "\<forall> j \<ge> i+2. ?a (j + 2) > ?a (j + 1)"
    proof safe
      fix j
      assume "i + 2 \<le> j"
      then have "?a j > 1" "?a (j + 1) > 1"
        using \<open>\<forall> j \<ge> i + 2. ?a j > 1\<close> \<open>i + 2 \<le> j\<close>
        by auto
      then have "?a (j + 1) < ?a j * ?a (j + 1)"
        by simp
      then show "?a (j + 2) > ?a (j + 1)"
        using eq
        by smt
    qed

    have "\<forall> j > i + 3. ?a j > ?a (i + 3)"
    proof safe
      fix j
      assume "i + 3 < j"
      then show "a ((i + 3) mod n) < a (j mod n)"
      proof (induction j)
        case 0
        then show ?case
          by simp
      next
        case (Suc j)
        show ?case
        proof (cases "i + 3 < j")
          case True
          then have "?a (i + 3) < ?a j"
            using Suc
            by simp
          also have "?a j < ?a (j + 1)"
            using Suc(2)
            using *[rule_format, of "j-1"]
            by simp
          finally
          show ?thesis
            by simp
        next
          case False
          then have "i + 3 = j"
            using Suc(2)
            by simp
          then show ?thesis
            using *[rule_format, of "i+2"]
            by (metis One_nat_def Suc_1 Suc_eq_plus1 add_Suc_right less_or_eq_imp_le numeral_3_eq_3)
        qed
      qed
    qed

    then have "?a (i + 3 + n) > ?a (i + 3)"
      by (meson assms less_add_same_cancel1 less_le_trans zero_less_numeral)

    moreover

    have "?a (i + 3 + n) = ?a (i + 3)"
      by simp

    ultimately

    show False
      by simp
  qed

  have no_zero: "\<forall> i. ?a i \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain i where "?a i = 0"
      by auto
    then have "?a (i + n) = 0"
      by auto
    have "?a (i + n + 2) = 1" 
      using \<open>?a (i + n) = 0\<close> eq
      by (metis add.commute mult_zero_left nat_arith.rule0)
    moreover
    have "?a (i + n + 1) = 1"
      using \<open>?a (i + n) = 0\<close> eq[rule_format, of "i+n-1"] \<open>n \<ge> 3\<close>
      by simp
    ultimately
    show False
      using no_pos_pos
      by (smt add.assoc one_add_one)
  qed

  have neg_neg_pos: "\<forall> i. ?a i < 0 \<and> ?a (i + 1) < 0 \<longrightarrow> ?a (i + 2) > 1"
    using eq
    by (smt mult_neg_neg)

  {
    fix i
    assume "?a i < 0" "?a (i + 1) < 0"
    then have "?a (i + 2) > 1"
      using neg_neg_pos
      by simp
    then have "?a (i + 3) < 0"
      using no_pos_pos no_zero
      by (smt One_nat_def Suc_eq_plus1 add_Suc_right numeral_3_eq_3 one_add_one)

    have "?a (i + 4) < 1"
    proof-
      have "?a (i + 4) = ?a (i+2) * ?a (i+3) + 1"
        using eq[rule_format, of "i+2"]
        by (simp add: numeral_3_eq_3 numeral_Bit0)
      moreover
      have "?a (i+2) * ?a (i + 3) < 0"
        using \<open>?a (i + 3) < 0\<close> \<open>?a (i + 2) > 1\<close>
        by (simp add: mult_pos_neg)
      ultimately
      show ?thesis
        by simp
    qed

    then have "?a (i + 4) < ?a (i + 2)"
      using \<open>?a (i + 2) > 1\<close>
      by simp

    have "?a (i+5) - ?a (i+4) = (?a (i+3) * ?a (i+4) + 1) - (?a (i+3) * ?a (i+2) + 1)"
      using eq
      by (simp add: Groups.mult_ac(2) numeral_eq_Suc)
    also have "... = ?a (i+3) * (?a (i+4) - ?a (i+2))"
      by (simp add: field_simps)
    finally have "?a (i+5) - ?a (i+4) > 0"
      using \<open>?a (i + 4) < ?a (i + 2)\<close> \<open>?a (i + 3) < 0\<close>
      by (smt mult_neg_neg)
    then have "?a (i + 5) > ?a (i + 4)"
      by auto
    then have "?a (i + 4) < 0"
      using no_pos_pos no_zero
      by (smt Suc_eq_plus1 add_Suc_right numeral_eq_Suc pred_numeral_simps(3))

    have "?a (i+2) > 0 \<and> ?a (i+3) < 0 \<and> ?a (i+4) < 0"
      using \<open>1 < a ((i + 2) mod n)\<close> \<open>a ((i + 3) mod n) < 0\<close> \<open>a ((i + 4) mod n) < 0\<close>
      by simp
  } note after_neg_neg = this

  have "\<exists> i. ?a i < 0 \<and> ?a (i + 1) < 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have alt: "\<forall> i. ?a i < 0 \<longleftrightarrow> ?a (i + 1) > 0"
      using no_zero no_pos_pos
      by smt

    have neg: "\<forall> i k. ?a i < 0 \<longrightarrow> ?a (i + 2*k) < 0"
    proof safe
      fix i k
      assume "?a i < 0"
      then show "?a (i + 2 * k) < 0"
      proof (induction k)
        case 0
        then show ?case
          by simp
      next
        case (Suc k)
        then show ?case
          using alt
          by (smt add.assoc add.commute mult_Suc_right no_zero one_add_one)
      qed
    qed

    have inc: "\<forall> i. ?a i < 0 \<longrightarrow> ?a i < ?a (i + 2)"
    proof safe
      fix i
      assume "?a i < 0"
      have "?a (i+1) > 0"
        using alt
        using \<open>?a i < 0\<close> 
        by blast
      then have "?a (i+2) < 0"
        using alt
        by (smt add.assoc no_zero one_add_one)
      then have "?a (i+3) > 0"
        using alt
        by (simp add: numeral_3_eq_3)
      have "?a i * ?a (i+1) + 1 < ?a (i+1) * ?a (i+2) + 1"
        using \<open>?a (i+2) < 0\<close> \<open>?a (i+3) > 0\<close> eq
        by (simp add: numeral_eq_Suc)
      then show "?a i < ?a (i + 2)"
        using \<open>?a (i + 1) > 0\<close>
        by (smt Groups.mult_ac(2) Suc_eq_plus1 add_2_eq_Suc' alt eq mult_less_cancel_left1)
    qed

    obtain i where "?a i < 0"
      using alt
      by (meson linorder_neqE_linordered_idom no_zero)
    have "\<forall> k \<ge> 1. ?a i < ?a (i + 2*k)"
    proof safe
      fix k::nat
      assume "1 \<le> k"
      then show "?a i < ?a (i + 2*k)"
      proof (induction k)
        case 0
        then show ?case
          by simp
      next
        case (Suc k)
        show ?case
        proof (cases "k = 0")
          case True
          then show ?thesis
            using inc \<open>?a i < 0\<close>
            by auto
        next
          case False
          then show ?thesis
            using \<open>?a i < 0\<close>
            using Suc(1) inc[rule_format, of "i + 2*k"] neg[rule_format, of i k]
            by simp
        qed
      qed
    qed
    then have "?a i < ?a (i + 2*n)"
      using \<open>n \<ge> 3\<close>
      by (simp add: numeral_eq_Suc)
    then show False
      by simp
  qed

  then obtain i where "?a i < 0" "?a (i + 1) < 0"
    by auto

  have neg_neg_pos: "\<forall> k. ?a (i + 3 * k) < 0 \<and> ?a (i + 1 + 3*k) < 0 \<and> ?a (i + 2 + 3*k) > 0" (is "\<forall> k. ?P k")
  proof
    fix k
    show "?P k"
    proof (induction k)
      case 0
      then show ?case
        using \<open>?a i < 0\<close> \<open>?a (i + 1) < 0\<close> after_neg_neg[of i]
        by simp
    next
      case (Suc k)
      then show ?case
        using after_neg_neg[of "i + 3*k"]
        using after_neg_neg[of "i + 3*k + 3"]
        by (simp add: numeral_3_eq_3 numeral_Bit0)
    qed
  qed

  show "3 dvd n"
  proof-
    have "n mod 3 = 0 \<or> n mod 3 = 1 \<or> n mod 3 = 2"
      by auto
    then show ?thesis
    proof
      assume "n mod 3 = 0"
      then show ?thesis
        by auto
    next
      assume "n mod 3 = 1 \<or> n mod 3 = 2"
      then have False
      proof
        assume "n mod 3 = 1"
        then obtain k where "n = 3 * k + 1"
          by (metis add_diff_cancel_left' add_diff_cancel_right' add_eq_if assms dvd_minus_mod dvd_mult_div_cancel not_numeral_le_zero plus_1_eq_Suc)
        then have "?a (i + 1) = ?a (i + 2 + 3*k)"
          by (metis add.assoc add_Suc_right mod_add_self2 one_add_one plus_1_eq_Suc)
        then show False
          using neg_neg_pos[rule_format, of 0] neg_neg_pos[rule_format, of k]
          by simp
      next
        assume "n mod 3 = 2"
        then obtain k where "n = 3 * k + 2"
          by (metis One_nat_def Suc_1 add.commute add_Suc_shift add_diff_cancel_left' assms dvd_minus_mod dvd_mult_div_cancel le_iff_add numeral_3_eq_3)
        then have "?a i = ?a (i + 2 + 3*k)"
          by (metis add.assoc add_Suc_right mod_add_self2 one_add_one plus_1_eq_Suc)
        then show False
          using neg_neg_pos[rule_format, of 0] neg_neg_pos[rule_format, of k]
          by simp
      qed
      then show ?thesis
        by simp
    qed
  qed
qed

end