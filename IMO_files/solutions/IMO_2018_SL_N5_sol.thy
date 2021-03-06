section \<open>Number theory problems\<close>

subsection \<open>IMO 2018 SL - N5\<close>

theory IMO_2018_SL_N5_sol
imports Main
begin

definition perfect_square :: "int \<Rightarrow> bool" where
  "perfect_square s \<longleftrightarrow> (\<exists> r. s = r * r)"

lemma perfect_square_root_pos:
  assumes "perfect_square s"
  shows "\<exists> r. r \<ge> 0 \<and> s = r * r"
  using assms
  unfolding perfect_square_def
  by (smt mult_minus_left mult_minus_right)

lemma not_perfect_square_15:
  fixes q::int
  shows "q^2 \<noteq> 15"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "3^2 < (abs q)^2" "(abs q)^2 < 4^2"
    by auto
  then have "3 < abs q" "abs q < 4"
    using abs_ge_zero power_less_imp_less_base zero_le_numeral
    by blast+
  then show False
    by simp
qed

lemma not_perfect_square_12:
  fixes q::int
  shows "q^2 \<noteq> 12"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "3^2 < (abs q)^2" "(abs q)^2 < 4^2"
    by auto
  then have "3 < abs q" "abs q < 4"
    using abs_ge_zero power_less_imp_less_base zero_le_numeral
    by blast+
  then show False
    by simp
qed

lemma not_perfect_square_8:
  fixes q::int
  shows "q^2 \<noteq> 8"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "2^2 < (abs q)^2" "(abs q)^2 < 3^2"
    by auto
  then have "2 < abs q" "abs q < 3"
    using abs_ge_zero power_less_imp_less_base zero_le_numeral
    by blast+
  then show False
    by simp
qed

lemma not_perfect_square_7:
  fixes q::int
  shows "q^2 \<noteq> 7"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "2^2 < (abs q)^2" "(abs q)^2 < 3^2"
    by auto
  then have "2 < abs q" "abs q < 3"
    using abs_ge_zero power_less_imp_less_base zero_le_numeral
    by blast+
  then show False
    by simp
qed

lemma not_perfect_square_5:
  fixes q::int
  shows "q^2 \<noteq> 5"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "2^2 < (abs q)^2" "(abs q)^2 < 3^2"
    by auto
  then have "2 < abs q" "abs q < 3"
    using abs_ge_zero power_less_imp_less_base zero_le_numeral
    by blast+
  then show False
    by simp
qed

lemma not_perfect_square_3:
  fixes q::int
  shows "q^2 \<noteq> 3"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "1^2 < (abs q)^2" "(abs q)^2 < 2^2"
    by auto
  then have "1 < abs q" "abs q < 2"
    using abs_ge_zero power_less_imp_less_base zero_le_numeral
    by blast+
  then show False
    by simp
qed

lemma IMO2018SL_N5_lemma:
  fixes s a b c d :: int
  assumes "s^2 = a^2 + b^2" "s^2 = c^2 + d^2" "2*s = a^2 - c^2" 
  assumes  "s > 0" "a \<ge> 0" "d \<ge> 0" "b \<ge> 0" "c \<ge> 0" "b > 0 \<or> c > 0" "b \<ge> c" 
  shows False
proof-
  have "2*s = d^2 - b^2"
    using assms
    by simp

  have "d > 0"
    using \<open>2 * s = d^2 - b^2\<close> \<open>s > 0\<close> \<open>d \<ge> 0\<close>
    by (smt pos_imp_zdiv_neg_iff zero_less_power2)

  have "a > 0"
    using \<open>2 * s = a^2 - c^2\<close> \<open>s > 0\<close> \<open>a \<ge> 0\<close>
    by (smt pos_imp_zdiv_neg_iff zero_less_power2)

  have "b > 0"
    using assms
    by auto

  have "d^2 > c^2"
    using \<open>2 * s = d\<^sup>2 - b\<^sup>2\<close> \<open>c \<le> b\<close> \<open>0 < s\<close>  \<open>c \<ge> 0\<close>
    by (smt power_mono)

  then have "d^2 > s^2 div 2"
    using \<open>s^2 = c^2 + d^2\<close>
    by presburger

  then have "2*s^2 < 4*d^2"
    by simp

  have "b < d"
    using \<open>2*s = d^2 - b^2\<close> \<open>s > 0\<close> \<open>d > 0\<close> \<open>b > 0\<close>
    by (smt power_mono_iff zero_less_numeral)

  have "even b \<longleftrightarrow> even d"
    using \<open>2*s = d^2 - b^2\<close>
    by (metis add_uminus_conv_diff dvd_minus_iff even_add even_mult_iff even_numeral power2_eq_square)

  then have "b \<le> d - 2"
    using \<open>b < d\<close>
    by (smt even_two_times_div_two odd_two_times_div_two_succ)

  then have "2*s \<ge> d^2 - (d-2)^2"
    using \<open>2*s = d^2 - b^2\<close> \<open>d > 0\<close> \<open>b > 0\<close>
    by auto
  then have "s \<ge> 2*(d - 1)"
    by (simp add: algebra_simps power2_eq_square)
  then have "2*d \<le> s + 2"
    by simp
  then have "4*d^2 \<le> (s + 2)^2"
    using abs_le_square_iff[of "2*d" "s + 2"] \<open>d > 0\<close> \<open>s > 0\<close>
    by auto
  then have "2*s^2 < (s+2)^2"
    using \<open>2*s^2 < 4*d^2\<close>
    by simp
  then have "(s - 2)^2 < 8"
    by (simp add: power2_eq_square algebra_simps)
  then have "(s - 2)^2 < 3^2"
    by simp
  then have "s - 2 < 3"
    using power2_less_imp_less
    by fastforce
  then have "s \<le> 4"
    by simp
  then have "s = 1 \<or> s = 2 \<or> s = 3 \<or> s = 4"
    using \<open>s > 0\<close>
    by auto
  moreover
  have "\<And> p q :: int. \<lbrakk>16 = p^2 + q^2; p \<ge> 0; q \<ge> 0\<rbrakk> \<Longrightarrow> p = 0 \<or> q = 0"
  proof-
    fix p q :: int
    assume "16 = p^2 + q^2" "p \<ge> 0" "q \<ge> 0"
    have "p \<le> 4"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "p \<ge> 5"
        by simp
      then have "p^2 \<ge> 25"
        using power_mono[of 5 p 2]
        by simp
      then have "p^2 + q^2 \<ge> 25"
        using zero_le_power2[of q]
        by linarith
      then show False
        using \<open>16 = p^2 + q^2\<close>
        by auto
    qed
    then have "p = 0 \<or> p = 1 \<or> p = 2 \<or> p = 3 \<or> p = 4"
      using \<open>0 \<le> p\<close>
      by auto
    then show "p = 0 \<or> q = 0"
      using \<open>16 = p^2 + q^2\<close> not_perfect_square_15 not_perfect_square_12 not_perfect_square_7
      by auto
  qed
  moreover
  have "\<And> p q :: int. \<lbrakk>9 = p^2 + q^2; p \<ge> 0; q \<ge> 0\<rbrakk> \<Longrightarrow> p = 0 \<or> q = 0"
  proof-
    fix p q :: int
    assume "9 = p^2 + q^2" "p \<ge> 0" "q \<ge> 0"
    have "p \<le> 3"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "p \<ge> 4"
        by simp
      then have "p^2 \<ge> 16"
        using power_mono[of 4 p 2]
        by simp
      then have "p^2 + q^2 \<ge> 16"
        using zero_le_power2[of q]
        by linarith
      then show False
        using \<open>9 = p^2 + q^2\<close>
        by auto
    qed
    then have "p = 0 \<or> p = 1 \<or> p = 2 \<or> p = 3"
      using \<open>0 \<le> p\<close>
      by auto
    then show "p = 0 \<or> q = 0"
      using \<open>9 = p^2 + q^2\<close> not_perfect_square_8 not_perfect_square_5
      by auto
  qed
  moreover
  have "\<And> p q :: int. \<lbrakk>4 = p^2 + q^2; p \<ge> 0; q \<ge> 0\<rbrakk> \<Longrightarrow> p = 0 \<or> q = 0"
  proof-
    fix p q :: int
    assume "4 = p^2 + q^2" "p \<ge> 0" "q \<ge> 0"
    have "p \<le> 2"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "p \<ge> 3"
        by simp
      then have "p^2 \<ge> 9"
        using power_mono[of 3 p 2]
        by simp
      then have "p^2 + q^2 \<ge> 9"
        using zero_le_power2[of q]
        by linarith
      then show False
        using \<open>4 = p^2 + q^2\<close>
        by auto
    qed
    then have "p = 0 \<or> p = 1 \<or> p = 2"
      using \<open>0 \<le> p\<close>
      by auto
    then show "p = 0 \<or> q = 0"
      using \<open>4 = p^2 + q^2\<close> not_perfect_square_3
      by auto
  qed
  moreover
  have "\<And> p q :: int. \<lbrakk>1 = p^2 + q^2; p \<ge> 0; q \<ge> 0\<rbrakk> \<Longrightarrow> p = 0 \<or> q = 0"
    by (smt one_le_power)
  moreover
  have "a \<noteq> 0" "d \<noteq> 0"
    using \<open>a > 0\<close> \<open>d > 0\<close>
    by auto
  ultimately
  have "c = 0" "b = 0"
    using \<open>s^2 = c^2 + d^2\<close> \<open>d \<ge> 0\<close> \<open>c \<ge> 0\<close> \<open>s^2 = a^2 + b^2\<close> \<open>a \<ge> 0\<close> \<open>b \<ge> 0\<close>
    by fastforce+
  then show False
    using \<open>b > 0 \<or> c > 0\<close>
    by auto
qed

theorem IMO2018SL_N5:
  fixes x y z t :: int
  assumes pos: "x > 0" "y > 0" "z > 0" "t > 0"
  assumes eq: "x*y - z*t = x + y" "x + y = z + t"
  shows " \<not> (perfect_square (x*y) \<and> perfect_square (z*t))"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain a c where "x*y = a*a" "z*t = c*c" "a > 0" "c > 0"
    using perfect_square_root_pos pos
    by (smt zero_less_mult_iff)

  show False
  proof (cases "odd (x + y)")
    case True

    have "even (x * y)"
      using True
      by auto

    moreover

    have "odd (z + t)"
      using True eq(2)
      by simp
    then have "even (z * t)"
      by auto

    ultimately

    have "even (x*y - z*t)"
      by simp
    then show False
      using eq(1) True
      by simp
  next
    case False
    then have "even (x + y)" "even (z + t)"
      using eq(2)
      by auto

    let ?s = "(x + y) div 2"
    let ?b = "abs (x - y) div 2" and ?d = "abs (z - t) div 2"

    have "?s ^ 2 = a ^ 2 + ?b ^ 2"
    proof-
      have "a^2 + ?b^2 = (x+y)^2 div 4"
        using \<open>even (x+y)\<close> div_power[of 2 "abs (x - y)" 2] \<open>x*y = a*a\<close>
        by (simp add: power2_eq_square algebra_simps)
      then show ?thesis
        by (metis False div_power mult_2_right numeral_Bit0 power2_eq_square)
    qed

    have "?s ^ 2 = c ^ 2 + ?d ^ 2"
    proof-
      have "c^2 + ?d^2 = (z+t)^2 div 4"
        using \<open>even (z+t)\<close> div_power[of 2 "abs (z - t)" 2] \<open>z*t = c*c\<close>
        by (simp add: power2_eq_square algebra_simps)
      then show ?thesis
        by (metis eq(2) False div_power mult_2_right numeral_Bit0 power2_eq_square)
    qed

    have "2*?s = a^2 - c^2"
      using \<open>even (x + y)\<close> \<open>x*y = a*a\<close> \<open>z*t = c*c\<close> eq(1)
      by (simp add: power2_eq_square)

    have "?s > 0"
      using \<open>x > 0\<close> \<open>y > 0\<close>
      by auto

    have "?b \<ge> 0" "?d \<ge> 0"
      by simp_all

    show ?thesis
    proof (cases "?b \<ge> c")
      case True
      then show False
        using IMO2018SL_N5_lemma[of "?s" a ?b c ?d]
        using \<open>?s^2 = a^2 + ?b^2\<close> \<open>?s^2 = c^2 + ?d^2\<close> \<open>2*?s = a^2 - c^2\<close>
        using \<open>a > 0\<close> \<open>c > 0\<close> \<open>?s > 0\<close> \<open>?d \<ge> 0\<close>
        by simp
    next
      case False
      then have "c \<ge> ?b"
        by simp
      then show False
        using IMO2018SL_N5_lemma[of "?s" ?d c ?b a]
        using \<open>?s^2 = a^2 + ?b^2\<close> \<open>?s^2 = c^2 + ?d^2\<close> \<open>2*?s = a^2 - c^2\<close>
        using \<open>a > 0\<close> \<open>c > 0\<close> \<open>?s > 0\<close> \<open>?b \<ge> 0\<close> \<open>?d \<ge> 0\<close>
        by simp
    qed
  qed
qed

end