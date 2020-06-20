theory IMO_2017_SL_N1_sol
imports Complex_Main
begin

lemma square_mod_3:
  fixes x :: nat
  shows "(x * x) mod 3 = 0 \<longleftrightarrow> x mod 3 = 0"
proof
  assume "x * x mod 3 = 0"
  show "x mod 3 = 0"
  proof-
    from division_decomp[of 3 x x] \<open>x * x mod 3 = 0\<close>
    obtain b c where "b * c = 3" "b dvd x" "c dvd x"
      by auto
    have "b \<le> 3 \<and> c \<le> 3"
      using \<open>b * c = 3\<close>
      by (metis One_nat_def le_add1 mult_eq_if mult_le_mono mult_numeral_1_right numerals(1) one_le_mult_iff order_refl zero_neq_numeral)
    then have "b \<in> {0, 1, 2, 3} \<and> c \<in> {0, 1, 2, 3}"
      by auto
    then have "(b = 1 \<and> c = 3) \<or> (b = 3 \<and> c = 1)"
      using \<open>b * c = 3\<close>
      by auto
    then show ?thesis
      using \<open>b dvd x\<close> \<open>c dvd x\<close>
      by auto
  qed
next
  assume "x mod 3 = 0"
  then show "x * x mod 3 = 0"
    by auto
qed


lemma square_mod_3_not_2:
  fixes s :: nat
  shows "(s * s) mod 3 \<noteq> 2"
proof-
  {
    assume "s mod 3 = 0"
    then have ?thesis
      by auto
  }

  moreover

  {
    assume "s mod 3 = 1"
    then have ?thesis
      by (metis mod_mult_right_eq mult.right_neutral numeral_eq_one_iff semiring_norm(85))
  }

  moreover

  {
    assume "s mod 3 = 2"
    then have ?thesis
      by (metis add_2_eq_Suc' calculation(2) eq_numeral_Suc less_add_same_cancel1 mod_add_self2 mod_less mod_mult_right_eq mult.commute mult_2 plus_1_eq_Suc pos2 pred_numeral_simps(3))
  }

  ultimately
  show ?thesis
    by presburger
qed

lemma not_square_3: 
  shows "\<not> (\<exists> s::nat. s * s = 3)"
  by (simp add: mult_eq_if)

lemma not_square_6: 
  shows "\<not> (\<exists> s::nat. s * s = 6)"
  by (simp add: mult_eq_if)

lemma not_square_7: 
  shows "\<not> (\<exists> s::nat. s * s = 7)"
  by (simp add: mult_eq_if)

lemma not_square_10: 
  shows "\<not> (\<exists> s::nat. s * s = 10)"
  by (simp add: mult_eq_if)

lemma not_square_13: 
  shows "\<not> (\<exists> s::nat. s * s = 13)"
  by (simp add: mult_eq_if)


lemma consecutive_squares_mod_3:
  fixes t :: nat
  shows "{(t + 1)\<^sup>2 mod 3, (t + 2)\<^sup>2 mod 3, (t + 3)\<^sup>2 mod 3} = {0, 1}"
proof-
  {
    assume "t mod 3 = 0"
    then obtain k where "t = 3 * k"
      by auto
    have "(t + 1)\<^sup>2 = 3*(3*k*k + 2*k) + 1"
      using \<open>t = 3 * k\<close>
      unfolding power2_eq_square
      by auto
    then have "(t + 1)\<^sup>2 mod 3 = 1"
      by presburger
    moreover
    have "(t + 2)\<^sup>2 = 3*(3*k*k + 4*k + 1) + 1"
      using \<open>t = 3 * k\<close>
      unfolding power2_eq_square
      by auto
    then have "(t + 2)\<^sup>2 mod 3 = 1"
      by presburger
    moreover
    have "(t + 3)\<^sup>2 = 3*(3*k*k + 6*k + 3)"
      using \<open>t = 3 * k\<close>
      unfolding power2_eq_square
      by (auto simp add: algebra_simps)
    then have "(t + 3)\<^sup>2 mod 3 = 0"
      by presburger
    ultimately
    have ?thesis
      by auto
  }
  moreover
  {
    assume "t mod 3 = 1"
    then obtain k where "t = 3 * k + 1"
      by (metis mult_div_mod_eq)
    have "(t + 1)\<^sup>2 = 3*(3*k*k + 4*k + 1) + 1"
      using \<open>t = 3 * k + 1\<close>
      unfolding power2_eq_square
      by auto
    then have "(t + 1)\<^sup>2 mod 3 = 1"
      by presburger
    moreover
    have "(t + 2)\<^sup>2 = 3*(3*k*k + 6*k + 3)"
      using \<open>t = 3 * k + 1\<close>
      unfolding power2_eq_square
      by auto
    then have "(t + 2)\<^sup>2 mod 3 = 0"
      by presburger
    moreover
    have "(t + 3)\<^sup>2 = 3*(3*k*k + 8*k+5) + 1"
      using \<open>t = 3 * k + 1\<close>
      unfolding power2_eq_square
      by (auto simp add: algebra_simps)
    then have "(t + 3)\<^sup>2 mod 3 = 1"
      by presburger
    ultimately
    have ?thesis
      by auto
  }
  moreover
  {
    assume "t mod 3 = 2"
    then obtain k where "t = 3 * k + 2"
      by (metis mult_div_mod_eq)
    have "(t + 1)\<^sup>2 = 3*(3*k*k + 6*k + 3)"
      using \<open>t = 3 * k + 2\<close>
      unfolding power2_eq_square
      by auto
    then have "(t + 1)\<^sup>2 mod 3 = 0"
      by presburger
    moreover
    have "(t + 2)\<^sup>2 = 3*(3*k*k + 8*k+5) + 1"
      using \<open>t = 3 * k + 2\<close>
      unfolding power2_eq_square
      by auto
    then have "(t + 2)\<^sup>2 mod 3 = 1"
      by presburger
    moreover
    have "(t + 3)\<^sup>2 = 3*(3*k*k+10*k+8)+1"
      using \<open>t = 3 * k + 2\<close>
      unfolding power2_eq_square
      by (auto simp add: algebra_simps)
    then have "(t + 3)\<^sup>2 mod 3 = 1"
      by presburger
    ultimately
    have ?thesis
      by auto
  }
  moreover
  have "t mod 3 = 0 \<or> t mod 3 = 1 \<or> t mod 3 = 2"
    by auto
  ultimately
  show ?thesis
    by metis
qed



definition eventually_periodic :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "eventually_periodic a \<longleftrightarrow> (\<exists> p > 0. \<exists> n0. \<forall> n \<ge> n0. a (n + p) = a n)"

lemma initial_condition:
  fixes a :: "nat \<Rightarrow> 'a"
  assumes "\<forall> n. a (n + 1) = f (a n)" "a n1 = a n2"
  shows "a (n1 + k) = a (n2 + k)"
  using assms
  by (induction k) auto

lemma two_same_periodic:
  fixes a :: "nat \<Rightarrow> 'a"
  assumes "\<forall> n. a (n + 1) = f (a n)" "n1 < n2" "a n1 = a n2"
  shows "eventually_periodic a"
proof-
  have "\<forall>n\<ge>n1. a (n + (n2 - n1)) = a n"
  proof safe
    fix n
    assume "n \<ge> n1"
    then show "a (n + (n2 - n1)) = a n"
      using initial_condition[of a f n2 n1 "n - n1"] assms \<open>n1 < n2\<close> \<open>a n1 = a n2\<close>
      by (simp add: add.commute)
  qed
  then show "eventually_periodic a"
    using \<open>n1 < n2\<close>
    unfolding eventually_periodic_def
    using zero_less_diff
    by blast
qed

lemma eventually_periodic_repeats:        
  fixes a :: "nat \<Rightarrow> 'a"
  assumes "\<forall> n \<ge> n0. a (n + p) = a n"
  shows "\<forall> k. a (n0 + k * p) = a n0"
proof
  fix k
  show "a (n0 + k * p) = a n0"
  proof (induction k)
    case 0 then show ?case by simp
  next
    case (Suc k)
    then show ?case
      using \<open>\<forall> n \<ge> n0. a (n + p) = a n\<close>[rule_format, of "n0 + k * p"]
      by (simp add: add.commute add.left_commute)
  qed
qed

lemma infinite_periodic:
  fixes a :: "nat \<Rightarrow> 'a"
  assumes "\<forall> n. a (n + 1) = f (a n)"
  shows "(\<exists> A. infinite {n. a n = A}) \<longleftrightarrow> eventually_periodic a"
proof
  assume "\<exists> A. infinite {n. a n = A}"
  then obtain A where "infinite {n. a n = A}"
    by auto
  then obtain n1 n2 where "n1 < n2" "a n1 = A" "a n2 = A"
    by (metis (full_types, lifting) bounded_nat_set_is_finite less_add_one mem_Collect_eq nat_neq_iff)
  then show "eventually_periodic a"
    using two_same_periodic[OF assms]
    by simp
next
  assume "eventually_periodic a"
  then obtain n0 p where "p > 0" "\<forall> n \<ge> n0. a (n + p) = a n"
    unfolding eventually_periodic_def
    by auto
  show "\<exists>A. infinite {n. a n = A}"
  proof (rule_tac x="a n0" in exI)
    have "(\<lambda> k. n0 + k * p) ` {n::nat. True} \<subseteq> {n. a n = a n0}"
      using eventually_periodic_repeats[OF `\<forall> n \<ge> n0. a (n + p) = a n`]
      by auto
    moreover
    have "infinite {n::nat. True}"
      by auto
    moreover
    have "inj_on (\<lambda> k. n0 + k * p) {n::nat. True}"
      using \<open>p > 0\<close>
      unfolding inj_on_def
      by auto
    ultimately
    show "infinite {n. a n = a n0}"
      using finite_subset[of "(\<lambda> k. n0 + k * p) ` {n::nat. True}" "{n. a n = a n0}"]
      using finite_image_iff
      by auto
  qed
qed

definition eventually_increasing :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "eventually_increasing a \<longleftrightarrow> (\<exists> n0. \<forall> n \<ge> n0. a n < a (n + 1))"

lemma eventually_increasing:
  shows "eventually_increasing a \<longleftrightarrow> (\<exists> n0. \<forall> i j. n0 \<le> i \<and> i < j \<longrightarrow> a i < a j)"
proof
  assume "eventually_increasing a"
  then obtain n0 where *: "\<forall> n \<ge> n0. a n < a (n + 1)"
    unfolding eventually_increasing_def
    by auto

  show "\<exists> n0. \<forall> i j. n0 \<le> i \<and> i < j \<longrightarrow> a i < a j"
  proof (rule_tac x="n0" in exI, safe)
    fix i j :: nat
    assume "n0 \<le> i" "i < j"
    then show "a i < a j"
    proof (induction k \<equiv> "j - i + 1" arbitrary: j)
      case 0
      then show ?case
        using *
        by auto
    next
      case (Suc k)
      show ?case
      proof (cases "i = j - 1")
        case True
        then show ?thesis
          using \<open>n0 \<le> i\<close> \<open>i < j\<close> *[rule_format, of "j-1"]
          by simp
      next
        case False
        then have "a i < a (j - 1)"
          using Suc
          by auto
        moreover
        have "a (j - 1) < a j"
          using \<open>n0 \<le> i\<close> \<open>i < j\<close> *[rule_format, of "j-1"]
          by simp
        ultimately
        show ?thesis
          by simp
      qed
    qed
  qed
next
  assume "\<exists> n0. \<forall>i j. n0 \<le> i \<and> i < j \<longrightarrow> a i < a j"
  then show "eventually_increasing a"
    unfolding eventually_increasing_def
    by auto
qed

lemma increasing_non_periodic:
  assumes "eventually_increasing a"
  shows "\<not> eventually_periodic a"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain p n0 where "p > 0" "\<forall> n \<ge> n0. a (n + p) = a n"
    using assms
    unfolding eventually_periodic_def
    by auto
  then show False
    using eventually_increasing[of a] assms
    by (metis add.left_neutral le_add1 le_add2 less_add_eq_less less_irrefl_nat)
qed

definition sqrt_nat :: "nat \<Rightarrow> nat" where 
  "sqrt_nat x = (THE s. x = s * s)"

lemma sqrt_nat:
  fixes x s :: nat
  assumes "x = s * s"
  shows "sqrt_nat x = s"
  unfolding sqrt_nat_def
proof (rule the_equality)
  show "x = s * s" by fact
next
  fix s'
  assume "x = s' * s'" 
  then show "s' = s" using assms
    by (metis le0 le_less_trans less_or_eq_imp_le mult_less_cancel2 nat_mult_less_cancel_disj nat_neq_iff)
qed

lemma Least_nat_in:
  fixes A :: "nat set"
  assumes "A \<noteq> {}"
  shows "(LEAST x. x \<in> A) \<in> A"
  using assms
  using Inf_nat_def Inf_nat_def1
  by auto

lemma Least_nat_le:
  fixes A :: "nat set"
  assumes "A \<noteq> {}"
  shows "\<forall> x \<in> A. (LEAST x. x \<in> A) \<le> x"
  by (simp add: Least_le)

theorem IMO_2017_SL_N1:
  fixes a :: "nat \<Rightarrow> nat"
  assumes "\<forall> n. a (n + 1) = (if (\<exists> s. a n  = s * s) then sqrt_nat (a n) else (a n) + 3)"
          "a 0 > 1"
  shows "(\<exists> A. infinite {n. a n = A}) \<longleftrightarrow> a 0 mod 3 = 0"
proof-
  have perfect_square: "\<And> n s. a n = s * s \<Longrightarrow> a (n + 1) = s"
    using sqrt_nat assms(1)
    by auto

  have not_perfect_square: "\<And> n. (\<nexists> s. a n = s * s) \<Longrightarrow> a (n + 1) = a n + 3"
    using sqrt_nat assms(1)
    by auto

  have gt1: "\<And> n. a n > 1"
  proof-
    fix n
    show "a n > 1"
    proof (induction n)
      case 0 then show ?case using \<open>a 0 > 1\<close> by simp
    next
      case (Suc n) 
      show ?case
      proof (cases "\<exists> s. a n = s * s")
        case True
        then obtain s where "a n = s * s" by auto
        then show ?thesis
          using Suc.IH perfect_square[of n s]
          by (metis One_nat_def Suc_lessI add.commute le_less_trans nat_0_less_mult_iff nat_1_eq_mult_iff plus_1_eq_Suc zero_le_one)
      next
        case False
        then show ?thesis
          using Suc.IH not_perfect_square
          by auto
      qed
    qed
  qed

  have mod3: "\<And>n n'. \<lbrakk>a n mod 3 = 0; n \<le> n'\<rbrakk> \<Longrightarrow> a n' mod 3 = 0"
  proof-
    fix n n'
    assume "a n mod 3 = 0" "n \<le> n'"
    then show "a n' mod 3 = 0"
    proof (induction k \<equiv> "n' - n" arbitrary: n')
      case 0
      then show ?case
        by simp
    next
      case (Suc k)
      then have "a (n' - 1) mod 3 = 0" "n' > 0"
        by auto
      show "a n' mod 3 = 0"
      proof (cases "\<exists> s. a (n' - 1) = s * s")
        case False
        then have "a n' = a (n' - 1) + 3"
          using not_perfect_square[of "n' - 1"] \<open>n' > 0\<close>
          by auto
        then show ?thesis
          using \<open>a (n' - 1) mod 3 = 0\<close>
          by auto
      next
        case True
        then obtain s where "a (n' - 1) = s * s"
          by auto
        then have "a n' = s"
          using perfect_square[of "n' - 1" s] \<open>n' > 0\<close>
          by auto
        then show ?thesis
          using \<open>a (n' - 1) mod 3 = 0\<close> \<open>a (n' - 1) = s * s\<close> square_mod_3[of s]
          by auto
      qed
    qed
  qed

  have not_mod3: "\<And>n n'. \<lbrakk>a n mod 3 \<noteq> 0; n \<le> n'\<rbrakk> \<Longrightarrow> a n' mod 3 \<noteq> 0"
  proof-
    fix n n'
    assume "a n mod 3 \<noteq> 0" "n \<le> n'"
    then show "a n' mod 3 \<noteq> 0"
    proof (induction k \<equiv> "n' - n" arbitrary: n')
      case 0
      then show ?case
        by simp
    next
      case (Suc k)
      then have "a (n' - 1) mod 3 \<noteq> 0" "n' > 0"
        by auto
      show ?case
      proof (cases "\<exists> s. a (n' - 1) = s * s")
        case True
        then obtain s where "a (n' - 1) = s * s"
          by auto
        then have "a n' = s"
          using perfect_square[of "n' - 1" s] \<open>n' > 0\<close>
          by auto
        then show ?thesis
          using \<open>a (n' - 1) = s * s\<close> \<open>a (n' - 1) mod 3 \<noteq> 0\<close> square_mod_3[of s]
          by auto
      next
        case False
        then have "a n' = a (n' - 1) + 3"
          using not_perfect_square[of "n' - 1"] \<open>n' > 0\<close>
          by auto
        then show ?thesis
          using \<open>a (n' - 1) mod 3 \<noteq> 0\<close>
          by auto
      qed
    qed
  qed

  have Claim1: "\<exists> n. a n mod 3 = 2 \<Longrightarrow> \<not> eventually_periodic a"
  proof-
    assume "\<exists> n. a n mod 3 = 2"
    then obtain n where "a n mod 3 = 2"
      by auto
    have "\<forall> m \<ge> n. \<not> (\<exists> s. a m = s * s) \<and> a m mod 3 = 2 \<and> a (m + 1) = a m + 3"
    proof (rule, rule)
      fix m
      assume "n \<le> m"
      then show "\<not> (\<exists> s. a m = s * s) \<and> a m mod 3 = 2 \<and> a (m + 1) = a m + 3"
        using \<open>a n mod 3 = 2\<close>
      proof (induction k \<equiv> "m - n" arbitrary: m)
        case 0
        then show ?case
          using square_mod_3_not_2 not_perfect_square[of m]
          by force
      next
        case (Suc k)
        then have "(\<nexists>s. a (m - 1) = s * s) \<and> a (m - 1) mod 3 = 2"
          by auto
        then have "a m = a (m - 1) + 3" "a m mod 3 = 2"
          using not_perfect_square[of "m-1"] \<open>Suc k = m - n\<close>
          by auto
        then show ?case
          using square_mod_3_not_2 not_perfect_square[of "m"]
          by metis
      qed
    qed
    then have "eventually_increasing a"
      unfolding eventually_increasing_def
      by force
    then show ?thesis
      by (simp add: increasing_non_periodic)
  qed

  have Claim2: "\<forall> n. a n mod 3 \<noteq> 2 \<and> a n > 9 \<longrightarrow> (\<exists> m > n. a m < a n)"
  proof safe
    fix n
    assume "a n mod 3 \<noteq> 2" "a n > 9"
    let ?T = "{t | t. t*t < a n}"
    have "finite ?T"
    proof (rule finite_subset)
      show "?T \<subseteq> {0..<a n}"
        by (smt atLeastLessThan_iff le_less_trans le_square less_eq_nat.simps(1) mem_Collect_eq subset_iff)
    qed simp
    have "3 \<in> ?T"
      using \<open>a n > 9\<close>
      by auto

    let ?t = "Max ?T"
    have "?t \<ge> 3"
      using \<open>finite ?T\<close> \<open>3 \<in> ?T\<close>
      by auto

    have "?t\<^sup>2 < a n"
      using \<open>finite ?T\<close> \<open>3 \<in> ?T\<close> Max_in[of ?T]
      by (metis (no_types, lifting) empty_iff mem_Collect_eq power2_eq_square)

    have "a n \<le> (?t + 1)\<^sup>2"
      using Max_ge[of ?T "?t + 1"] \<open>finite ?T\<close>
      by (metis (no_types, lifting) add.right_neutral add_le_imp_le_left mem_Collect_eq not_less not_one_le_zero power2_eq_square)

    have "\<exists> k. a (n + k) \<in> {(?t+1)\<^sup>2, (?t+2)\<^sup>2, (?t+3)\<^sup>2}"
    proof-
      {
        fix t i
        assume "t\<^sup>2 < a n" "a n \<le> (t+1)\<^sup>2" "i > 0"
               "\<forall> i'. 0 < i' \<and> i' < i \<longrightarrow> a n mod 3 \<noteq> (t + i')\<^sup>2 mod 3"
               "a n mod 3 = (t + i)\<^sup>2 mod 3" 

        let ?k = "((t + i)\<^sup>2 - a n) div 3"

        have "a n \<le> (t + i)\<^sup>2"
          using \<open>a n \<le> (t + 1)\<^sup>2\<close> \<open>i > 0\<close>
          by (metis add_le_imp_le_left gr_implies_not0 le_neq_implies_less le_trans less_one nat_le_linear power2_nat_le_eq_le)

        have "3 dvd ((t + i)\<^sup>2 - a n)"
          using \<open>a n mod 3 = (t + i)\<^sup>2 mod 3\<close> \<open>a n \<le> (t + i)\<^sup>2\<close>
          using mod_eq_dvd_iff_nat
          by fastforce
        then have "3 * (((t + i)\<^sup>2 - a n) div 3) = (t + i)\<^sup>2 - a n"
          by simp

        have 1: "\<forall> k' \<le> ?k. a (n + k') = a n + 3 * k'"
        proof safe
          fix k'
          assume "k' \<le> ?k"
          then show "a (n + k') = a n + 3 * k'"
          proof (induction k')
            case 0 then show ?case by simp
          next
            case (Suc k')
            then have "a (n + k') = a n + 3 * k'"
              by auto
            have "\<not> (\<exists> s. a (n + k') = s * s)"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then obtain s where "a (n + k') = s * s" by auto

              have "3 * (k' + 1) \<le> (t + i)\<^sup>2 - a n"
                using Suc(2)
                using \<open>3 * (((t + i)\<^sup>2 - a n) div 3) = (t + i)\<^sup>2 - a n\<close>
                by simp
              then have "a (n + k') < (t + i)\<^sup>2"
                using \<open>a (n + k') = a n + 3 * k'\<close>
                by simp
              moreover 
              have "a (n + k') > t\<^sup>2"
                using \<open>a (n + k') = a n + 3 * k'\<close> \<open>a n > t\<^sup>2\<close>
                by simp
              ultimately
              have "t\<^sup>2 < s\<^sup>2 \<and> s\<^sup>2 < (t + i)\<^sup>2"
                using \<open>a (n + k') = s * s\<close>
                by (simp add: power2_eq_square)
              then have "t < s \<and> s < t + i"
                using power_less_imp_less_base by blast
              then obtain i' where "0 < i'" "i' < i"  "s = t + i'"
                using less_imp_add_positive by auto

              moreover

              have "\<forall> i'. 0 < i' \<and> i' < i \<longrightarrow> a (n + k') \<noteq> (t + i')\<^sup>2"
                using \<open>a (n + k') = a n + 3 * k'\<close> \<open>\<forall> i'. 0 < i' \<and> i' < i \<longrightarrow> a n mod 3 \<noteq> (t + i')\<^sup>2 mod 3\<close>
                by fastforce

              ultimately

              show False
                using \<open>a (n + k') = s * s\<close>
                by (auto simp add: power2_eq_square)
            qed
            then show ?case
              using not_perfect_square[of "n + k'"] \<open>a (n + k') = a n + 3 * k'\<close>
              by auto
          qed
        qed

        have "a (n + ?k) = (t + i)\<^sup>2"
          using 1[rule_format, of ?k] \<open>a n \<le> (t + i)\<^sup>2\<close> \<open>3 * (((t + i)\<^sup>2 - a n) div 3) = (t + i)\<^sup>2 - a n\<close>
          by simp
        then have "\<exists> k. a (n + k) = (t + i)\<^sup>2"
          by blast
      } note ti = this

      have "a n mod 3 = 0 \<or> a n mod 3 = 1"
        using \<open>a n mod 3 \<noteq> 2\<close>
        by auto
      then have cc: "a n mod 3 = (?t+1)\<^sup>2 mod 3 \<or> a n mod 3 = (?t+2)\<^sup>2 mod 3 \<or> a n mod 3 = (?t+3)\<^sup>2 mod 3"
        using consecutive_squares_mod_3[of ?t]
        by (smt empty_iff insert_iff)

      show ?thesis
      proof (cases "a n mod 3 = (?t+1)\<^sup>2 mod 3")
        case True
        then show ?thesis
          using ti[of ?t 1] \<open>?t\<^sup>2 < a n\<close> \<open>a n \<le> (?t + 1)\<^sup>2\<close>
          by auto
      next
        case False
        then have "\<forall>i'. 0 < i' \<and> i' < 2 \<longrightarrow> a n mod 3 \<noteq> (?t + i')\<^sup>2 mod 3"
          by (metis mod2_gr_0 mod_less)
        show ?thesis
        proof (cases "a n mod 3 = (?t+2)\<^sup>2 mod 3")
          case True
          then show ?thesis
            using ti[of ?t 2] \<open>?t\<^sup>2 < a n\<close>  \<open>a n \<le> (?t + 1)\<^sup>2\<close> \<open>\<forall>i'. 0 < i' \<and> i' < 2 \<longrightarrow> a n mod 3 \<noteq> (?t + i')\<^sup>2 mod 3\<close>
            by auto
        next
          case False
          have "a n mod 3 = (?t + 3)\<^sup>2 mod 3"
            using \<open>a n mod 3 \<noteq> (?t + 1)\<^sup>2 mod 3\<close>  \<open>a n mod 3 \<noteq> (?t + 2)\<^sup>2 mod 3\<close>
            using cc
            by auto
          moreover
          have "\<forall>i'. 0 < i' \<and> i' < 3 \<longrightarrow> a n mod 3 \<noteq> (?t + i')\<^sup>2 mod 3"
            using \<open>a n mod 3 \<noteq> (?t + 1)\<^sup>2 mod 3\<close>  \<open>a n mod 3 \<noteq> (?t + 2)\<^sup>2 mod 3\<close>
            by (metis (mono_tags, lifting) One_nat_def Suc_1 linorder_neqE_nat not_less_eq numeral_3_eq_3)
          ultimately
          show ?thesis
            using ti[of ?t 3] \<open>?t\<^sup>2 < a n\<close> \<open>a n \<le> (?t + 1)\<^sup>2\<close>
            by auto
        qed
      qed
    qed
    then obtain k where "a (n + k) \<in> {(?t+1)\<^sup>2, (?t+2)\<^sup>2, (?t+3)\<^sup>2}"
      by auto
    have "a (n + k + 1) \<le> ?t + 3"
    proof-
      have "a (n + k + 1) = ?t + 1 \<or> a (n + k + 1) = ?t + 2 \<or> a (n + k + 1) = ?t + 3"
        using \<open>a (n + k) \<in> {(?t+1)\<^sup>2, (?t+2)\<^sup>2, (?t+3)\<^sup>2}\<close>
        unfolding power2_eq_square
        using perfect_square
        by auto
      then show ?thesis
        by auto
    qed
    also have "... < ?t * ?t"
    proof-
      {
        fix t::nat
        assume "t \<ge> 3"
        then have "t + 3 < t * t"
          using div_nat_eqI le_add1 mult_eq_if
          by auto
      } then show ?thesis
        using \<open>?t \<ge> 3\<close>
        by simp
    qed
    also have "... < a n"
    proof-
      have "?t \<in> ?T"
      proof (rule Max_in)
        show "finite ?T" by fact
      next
        show "?T \<noteq> {}"
          using \<open>3 \<in> ?T\<close>
          by blast
      qed
      then show ?thesis
        by auto
    qed
    finally show "\<exists>m>n. a m < a n"
      using add_lessD1 less_add_one by blast
  qed

  have Claim3_a: "\<forall> n. a n mod 3 = 0 \<and> a n \<le> 9 \<longrightarrow> (\<exists> m > n. a m = 3)"
  proof safe
    fix n
    assume "3 dvd a n" "a n \<le> 9"
    then have "a n = 3 \<or> a n = 6 \<or> a n = 9"
      using \<open>3 dvd a n\<close> gt1[of n]
      by auto
    show "\<exists>m>n. a m = 3"
    proof-
      have "\<And> n. a n = 3 \<Longrightarrow> a (n + 1) = 6"
        using not_perfect_square not_square_3
        by (auto split: if_split_asm)

      moreover

      have "\<And> n. a n = 6 \<Longrightarrow> a (n + 1) = 9"
        using not_perfect_square not_square_6
        by (auto split: if_split_asm)

      moreover

      have "\<And> n. a n = 9 \<Longrightarrow> a (n + 1) = 3"
        using perfect_square
        by simp

      ultimately
      show ?thesis
        using \<open>a n = 3 \<or> a n = 6 \<or> a n = 9\<close>
        by (meson add_lessD1 less_add_one)
    qed
  qed

  have Claim3: "\<forall> n. a n mod 3 = 0 \<longrightarrow> (\<exists> m > n. a m = 3)"
  proof safe
    fix n
    assume "3 dvd a n"
    show "\<exists> m > n. a m = 3"
    proof (cases "a n \<le> 9")
      case True
      then show ?thesis
        using \<open>3 dvd a n\<close> Claim3_a
        by auto
    next
      case False
      let ?m = "LEAST x. x \<in> (a ` {n+1..})"
      let ?j = "SOME j. j > n \<and> a j = ?m"
      have "\<exists> j. j > n \<and> a j = ?m"
        using Least_nat_in[of "a ` {n+1..}"]
        by (smt atLeast_iff imageE image_is_empty less_add_one less_le_trans not_Ici_eq_empty)
      then have "?j > n" "a ?j = ?m"
        using someI_ex[of "\<lambda> j. j > n \<and> a j = ?m"]
        by auto
      show ?thesis
      proof (cases "a ?j \<le> 9")
        case True
        then show ?thesis
          using Claim3_a[rule_format, of "?j"] mod3[of n "?j"] \<open>?j > n\<close> \<open>3 dvd a n\<close>
          by (meson dvd_imp_mod_0 less_trans nat_less_le)
      next
        case False
        have "a ?j mod 3 \<noteq> 2"
          using \<open>3 dvd a n\<close> mod3[of n ?j] \<open>n < ?j\<close>
          by simp
        then obtain m where "m > ?j" "a m < a ?j"
          using Claim2[rule_format, of ?j] False
          by auto
        then have "m > n" "a m < ?m"
          using \<open>n < ?j\<close> \<open>a ?j = ?m\<close>
          by auto
        then have False
          using Least_nat_le[of "a ` {n + 1..}", rule_format, of "a m"]
          by simp
        then show ?thesis
          by simp
      qed
    qed
  qed

  have Claim4_a: "\<forall> n. a n mod 3 = 1 \<and> a n \<le> 9 \<longrightarrow> (\<exists> m > n. a m mod 3 = 2)"
  proof safe
    fix n
    assume "a n mod 3 = 1" "a n \<le> 9"
    then have "a n = 2 \<or> a n = 3 \<or> a n = 4 \<or> a n = 5 \<or> a n = 6 \<or> a n = 7 \<or> a n = 8 \<or> a n = 9"
      using gt1[of n] 
      by auto
    then have "a n = 4 \<or> a n = 7"
      using \<open>a n mod 3 = 1\<close>
      by auto
    then show "\<exists> m > n. a m mod 3 = 2"
    proof
      assume "a n = 4"
      then have "a (n + 1) = 2"
        using perfect_square[of n 2]
        by simp
      then show ?thesis
        by force
    next
      assume "a n = 7"
      then have "a (n + 1) = 10"
        using not_square_7 not_perfect_square
        by auto
      then have "a (n + 2) = 13"
        using not_square_10 not_perfect_square
        by auto
      then have "a (n + 3) = 16"
        using not_square_13 assms(1)
        by (simp add: numeral_3_eq_3)
      then have "a (n + 4) = 4"
        using perfect_square[of "n+3" 4]
        by (auto simp add: add.commute)
      then have "a (n + 5) = 2"
        using perfect_square[of "n+4" 2]
        by (auto simp add: add.commute)
      then show ?thesis
        by (rule_tac x="n+5" in exI, simp)
    qed
  qed

  have Claim4: "\<forall> n. a n mod 3 = 1 \<longrightarrow> (\<exists> m > n. a m mod 3 = 2)"
  proof safe
    fix n
    assume "a n mod 3 = 1"
    show "\<exists>m>n. a m mod 3 = 2"
    proof (cases "a n < 10")
      case True
      then show ?thesis
        using Claim4_a \<open>a n mod 3 = 1\<close>
        by auto
    next
      case False
      let ?m = "LEAST x. x \<in> (a ` {n+1..})"
      let ?j = "SOME j. j > n \<and> a j = ?m"
      have "\<exists> j. j > n \<and> a j = ?m"
        using Least_nat_in[of "a ` {n+1..}"]
        by (smt atLeast_iff imageE image_is_empty less_add_one less_le_trans not_Ici_eq_empty)
      then have "?j > n" "a ?j = ?m"
        using someI_ex[of "\<lambda> j. j > n \<and> a j = ?m"]
        by auto
      {
        assume "a ?j mod 3 = 1"
        have ?thesis
        proof (cases "a ?j \<le> 9")
          case False
          then obtain m where "m > ?j" "a m < a ?j"
            using Claim2[rule_format, of "?j"] \<open>a ?j mod 3 = 1\<close>
            by auto
          then have "m > n" "a m < ?m"
            using \<open>n < ?j\<close> \<open>a ?j = ?m\<close>
            by auto
          then have False
            using Least_nat_le[of "a ` {n + 1..}", rule_format, of "a m"]
            by simp
          then show ?thesis
            by simp
        next
          case True
          then show ?thesis
            using Claim4_a[rule_format, of ?j] \<open>a ?j mod 3 = 1\<close> \<open>n < ?j\<close>
            using less_trans
            by blast
        qed
      }

      moreover

      have "a ?j mod 3 = 2 \<Longrightarrow> ?thesis"
        using \<open>?j > n\<close>
        by force

      moreover
      {
        have "a ?j mod 3 \<noteq> 0"
          using not_mod3[of n ?j] \<open>a n mod 3 = 1\<close> \<open>n < ?j\<close>
          by auto
      }

      moreover
      have "a ?j mod 3 < 3"
        by auto
      then have "a ?j mod 3 = 0 \<or> a ?j mod 3 = 1 \<or> a ?j mod 3 = 2"
        by auto
      ultimately

      show ?thesis
        by auto
    qed
  qed

  show ?thesis
  proof
    assume "a 0 mod 3 = 0"
    then have "eventually_periodic a"
      using Claim3 two_same_periodic[OF assms(1)]
      by (metis mod_self)
    then show "\<exists> A. infinite {n. a n = A}"
      by (simp add: infinite_periodic[OF assms(1)])
  next
    assume "\<exists> A. infinite {n. a n = A}"
    then have "eventually_periodic a"
      by (simp add: infinite_periodic[OF assms(1)])
    {
      assume "a 0 mod 3 = 1"
      then obtain m where "a m mod 3 = 2"
        using Claim4
        by auto
      then have False
        using Claim1 \<open>eventually_periodic a\<close>
        by force
    }
    moreover
    {
      assume "a 0 mod 3 = 2"
      then have False
        using Claim1 \<open>eventually_periodic a\<close>
        by force
    }
    ultimately
    show "a 0 mod 3 = 0"
      by presburger
  qed
qed

end