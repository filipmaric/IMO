theory IMO_2018_SL_C4
  imports Main "HOL-Library.Permutation"
begin

definition antipascal :: "(nat \<Rightarrow> nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> bool" where
   "antipascal f n \<longleftrightarrow> (\<forall> r < n. \<forall> c \<le> r. f r c = abs (f (r+1) c - f (r+1) (c+1)))"

definition triangle :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
  "triangle r0 c0 n = {(r, c) | r c :: nat. r0 \<le> r \<and> r < r0 + n \<and> c0 \<le> c \<and> c \<le> c0 + r - r0}"

lemma triangle_finite [simp]:
  shows "finite (triangle r0 c0 n)"
proof-
    have "triangle r0 c0 n \<subseteq> {0..<r0 + n} \<times> {0..<c0 + n}"
      unfolding triangle_def
      by auto
    thus ?thesis
      using finite_atLeastLessThan infinite_super
      by blast
qed

lemma triangle_card:
  shows "card (triangle r0 c0 n) = n * (n+1) div 2"
proof (induction n arbitrary: r0 c0)
  case 0
  have *: "{(i, j). r0 \<le> i \<and> i < r0 \<and> c0 \<le> j \<and> j \<le> c0 + i - r0} = {}"
    by auto
  thus ?case
    using 0
    unfolding triangle_def
    by (simp add: *)
next
  case (Suc n)
  let ?row = "{(r0 + n, j) | j. c0 \<le> j \<and> j < c0 + Suc n}"
  have "triangle r0 c0 (Suc n) = triangle r0 c0 n \<union> ?row"
    unfolding triangle_def
    by auto
  moreover
  have "triangle r0 c0 n \<inter> ?row = {}"
    unfolding triangle_def
    by auto
  ultimately
  have "card (triangle r0 c0 (Suc n)) = card (triangle r0 c0 n) + card ?row"
    by (simp add: card_Un_disjoint)
  moreover
  have "card ?row = Suc n"
  proof-
    have "?row = (\<lambda> j. (r0 + n, j)) ` {c0..<c0 + Suc n}"
      by auto
    moreover
    have "inj_on (\<lambda> j. (r0 + n, j)) {c0..<c0 + Suc n}"
      unfolding inj_on_def
      by auto
    hence "card ((\<lambda> j. (r0 + n, j)) ` {c0..<c0 + Suc n}) = card {c0..<c0 + Suc n}"
      using card_image
      by blast
    hence "card ((\<lambda> j. (r0 + n, j)) ` {c0..<c0 + Suc n}) = Suc n"
      by auto
    ultimately
    show ?thesis
      by simp
  qed
  ultimately
  have "card (triangle r0 c0 (Suc n)) = (n * (n + 1)) div 2 + Suc n"
    using Suc
    by simp
  thus ?case
    by auto
qed

fun uncurry where
   "uncurry f (a, b) = f a b"

lemma gauss: 
  fixes n :: nat
  shows "sum_list [1..<n] = n * (n - 1) div 2"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "sum_list [1..<Suc n] = sum_list [1..<n] + n"
    by simp
  also have "... = n * (n - 1) div 2 + n"
    using Suc
    by simp
  finally
  show ?case
    by (metis Sum_Ico_nat diff_self_eq_0 distinct_sum_list_conv_Sum distinct_upt minus_nat.diff_0 mult_eq_0_iff set_upt)
qed

lemma sum_list_insort [simp]:
  fixes x :: nat and xs :: "nat list"
  shows "sum_list (insort x xs) = x + sum_list xs"
  by (induction xs, auto)

lemma sum_list_sort [simp]:
  fixes xs :: "nat list"
  shows "sum_list (sort xs) = sum_list xs"
  by (induction xs, auto)

lemma sorted_distinct_strict_increase:
  assumes "sorted (xs @ [x])" "distinct (xs @ [x])" "\<forall> x \<in> set (xs @ [x]). x > a"
  shows "x > a + length xs"
  using assms
proof (induction xs arbitrary: x rule: rev_induct)
  case Nil
  thus ?case
    by simp
next
  case (snoc x' xs)
  show ?case
    using snoc(1)[of x'] snoc(2-)
    by (auto simp add: sorted_append)
qed

lemma sum_list_sorted_distinct_lb:
  assumes "\<forall> x \<in> set xs. x > a" "distinct xs" "sorted xs"
  shows "sum_list xs \<ge> length xs * (2 * a + length xs + 1) div 2"
  using assms            
proof (induction xs rule: rev_induct)
  case Nil
  thus ?case
    by simp
next
  case (snoc x xs)
  have "x > a + length xs"
    using sorted_distinct_strict_increase[of xs x a]
    using snoc(2-)
    by auto
  moreover
  have "length xs * (2 * a + length xs + 1) div 2 \<le> sum_list xs"
    using snoc
    by (auto simp add: sorted_append)
  ultimately
  show ?case
    by auto
qed

lemma sum_list_distinct_lb:
  assumes "\<forall> x \<in> set xs. f x > a" "distinct (map f xs)"
  shows "(\<Sum> x \<leftarrow> xs. f x) \<ge> length xs * (2 * a + length xs + 1) div 2"
  using assms
  using sum_list_sorted_distinct_lb[of "sort (map f xs)" a]
  by simp

lemma consecutive_nats_sorted:
  assumes "sorted xs" "length xs = n" "distinct xs" "sum_list xs \<le> n * (n + 1) div 2" "\<forall> x \<in> set xs. x > 0"
  shows "xs = [1..<n+1]"
  using assms
proof (induction xs arbitrary: n rule: rev_induct)
  case Nil
  thus ?case
    by simp
next
  case (snoc x xs)
  have "n > 0"
    using `length (xs @ [x]) = n`
    by simp
  have "xs = [1..<(n-1)+1]"
  proof (rule snoc(1))
    show "sorted xs" "length xs = n-1" "distinct xs" "\<forall>a\<in>set xs. 0 < a"
      using snoc(2-6)
      by (auto simp add: sorted_append)
    show "sum_list xs \<le> (n - 1) * (n - 1 + 1) div 2"
    proof-
      have "x \<ge> n"
        using snoc(2-4) snoc(6)
      proof (induction xs arbitrary: x n rule: rev_induct)
        case Nil
        thus ?case
          by simp
      next
        case (snoc x' xs')
        have "n-1 \<le> x'"
          using snoc(1)[of x' "n-1"] snoc(2-)
          by (simp add: sorted_append)
        moreover
        have "x > x'"
          using snoc(2) snoc(4)
          by (simp add: sorted_append)
        ultimately
        show ?case
          by simp
      qed
      show ?thesis
      proof-
        have "sum_list xs \<le> n * (n + 1) div 2 - x"
          using snoc(5)
          by simp
        also have "... \<le> n * (n + 1) div 2 - n"
          using `n \<le> x`
          by simp
        also have "... = n * (n - 1) div 2"
          by (simp add: diff_mult_distrib2)
        finally
        show ?thesis
          using `n > 0`
          by (auto simp add: mult.commute)
      qed
    qed
  qed
  hence "xs = [1..<n]"
    using `n > 0`
    by simp
  hence "x \<ge> n"
    using snoc(2) snoc(4) snoc(6)
    by (auto simp add: sorted_append)
  have "x = n"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "x > n"
      using `x \<ge> n`
      by simp
    hence "sum_list (xs @ [x]) > n * (n - 1) div 2 + n"
      using `xs = [1..<n]` gauss[of n]
      by simp
    thus False
      using snoc(5)
      by (smt Suc_diff_1 \<open>0 < n\<close> add.commute add_Suc_right distrib_left div_mult_self2 less_le_trans mult_2 mult_2_right nat_neq_iff one_add_one plus_1_eq_Suc zero_neq_numeral)
  qed
  thus ?case
    using `xs = [1..<n]`
    by (simp add: Suc_leI \<open>0 < n\<close>)
qed
  
lemma consecutive_nats:
  assumes "length xs = n" "distinct xs" "sum_list xs \<le> n * (n + 1) div 2" "\<forall> x \<in> set xs. x > 0"
  shows "set xs = {1..<n+1}"
proof-
  have "sort xs = [1..<n+1]"
    using consecutive_nats_sorted[of "sort xs" n] assms
    by simp 
  thus ?thesis
    by (metis set_sort set_upt)
qed

lemma sum_list_cong:
  assumes "\<forall> x \<in> set xs. f x = g x"
  shows "(\<Sum> x \<leftarrow> xs. f x) = (\<Sum> x \<leftarrow> xs. g x)"
  using assms
  by (induction xs, auto)

lemma sum_list_last:
  assumes "a \<le> b"
  shows "(\<Sum> x \<leftarrow> [a..<b+1]. f x) = (\<Sum> x \<leftarrow> [a..<b]. f x) + f b"
proof-
  have *: "[a..<b+1] = [a..<b] @ [b]"
    using assms
    by auto
  show ?thesis
    by (subst *, simp)
qed

lemma sum_list_nat:
  assumes "\<forall> x \<in> set xs. f x \<ge> 0"
  shows "(\<Sum> x \<leftarrow> xs. nat (f x)) = (nat (\<Sum> x \<leftarrow> xs. f x))"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  thus ?case
    using sum_list_mono
    by fastforce
qed

theorem "\<nexists> f. antipascal f 2018 \<and> 
            (uncurry f) ` triangle 0 0 2018  = {1..<2018*(2018 + 1) div 2 + 1}"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain f where
   f: "antipascal f 2018" "(uncurry f) ` triangle 0 0 2018 = {1..<2018*(2018 + 1) div 2+1}"
    by auto

  have "inj_on (uncurry f) (triangle 0 0 2018)"
  proof (rule eq_card_imp_inj_on)
    show "finite (triangle 0 0 2018)"
      by simp
  next
    show "card ((uncurry f) ` triangle 0 0 2018) = card (triangle 0 0 2018)"
      using f(2) triangle_card
      by simp
  qed

  have path: "\<forall> r0 < 2018. \<forall> c0 \<le> r0. \<forall> n. r0 + n \<le> 2018 \<longrightarrow> (\<exists> a b. a r0 = c0 \<and> b r0 = c0 \<and> 
                    (\<forall> r. r0 < r \<and> r < r0 + n \<longrightarrow> 
                         a r \<noteq> b r \<and> c0 \<le> a r \<and> a r \<le> c0 + (r - r0) \<and> c0 \<le> b r \<and> b r \<le> c0 + (r - r0) \<and>
                         (a r = b (r - 1) \<or> a r = b (r - 1) + 1) \<and> 
                         (b r = b (r - 1) \<or> b r = b (r - 1) + 1)) \<and> 
                    (\<forall> r. r0 \<le> r \<and> r < r0 + n \<longrightarrow> f r (b r) = (\<Sum> r' \<leftarrow> [r0..<r+1]. f r' (a r'))))" (is "\<forall> r0 < 2018. \<forall> c0 \<le> r0. \<forall> n. r0 + n \<le> 2018 \<longrightarrow> ?P r0 c0 n")
  proof safe
    fix r0 c0 n :: nat
    assume "r0 < 2018" "c0 \<le> r0" "r0 + n \<le> 2018"
    then show "?P r0 c0 n"
    proof (induction n)
      case 0
      thus ?case
        by auto
    next
      case (Suc n)

      show ?case
      proof (cases "n = 0")
        case True
        thus ?thesis
          by auto
      next
        case False
        show ?thesis
        proof-
          obtain a b where *:
            "a r0 = c0" "b r0 = c0"
            "\<forall>r. r0 < r \<and> r < r0 + n \<longrightarrow>
                   a r \<noteq> b r \<and>
                   c0 \<le> a r \<and> a r \<le> c0 + (r - r0) \<and>
                   c0 \<le> b r \<and> b r \<le> c0 + (r - r0) \<and>
                   (a r = b (r - 1) \<or> a r = b (r - 1) + 1) \<and>
                   (b r = b (r - 1) \<or> b r = b (r - 1) + 1)"
            "\<forall>r. r0 \<le> r \<and> r < r0 + n \<longrightarrow> f r (b r) = (\<Sum>r'\<leftarrow>[r0..<r + 1]. f r' (a r'))"
            using Suc
            by auto

          have ap': "\<forall>r c. r0 \<le> r \<and> r \<le> r0 + n \<and> c0 \<le> c \<and> c < c0 + (r - r0) \<longrightarrow> f (r - 1) c = \<bar>f r c - f r (c + 1)\<bar>"
            using `antipascal f 2018` `n \<noteq> 0` Suc(3-4)
            unfolding antipascal_def
            by auto
          have ap: "f (r0 + n - 1) (b (r0 + n - 1)) = \<bar>f (r0 + n) (b (r0 + n - 1)) - f (r0 + n) (b (r0 + n - 1) + 1)\<bar>"
          proof (cases "n = 1")
            case True
            thus ?thesis
              using *(2) ap'[rule_format, of "r0 + 1"]
              by simp
          next
            case False
            hence "n > 1"
              using `n \<noteq> 0`
              by simp
            show ?thesis
            proof (subst ap')
              have "r0 < r0 + n - 1"
                using `n > 1`
                by simp
              hence "b (r0 + n - Suc 0) \<le> c0 + n - Suc 0"
                using *(3)[rule_format, of "r0 + n - 1"] `n > 1`
                by simp
              then show "r0 \<le> r0 + n \<and> r0 + n \<le> r0 + n \<and> c0 \<le> b (r0 + n - 1) \<and> b (r0 + n - 1) < c0 + (r0 + n - r0)"
                using *(3)[rule_format, of "r0 + n - 1"] `n > 1`
                by simp
            qed simp
          qed

          let ?an = "if f (r0 + n) (b (r0 + n - 1)) < f (r0 + n) (b (r0 + n - 1) + 1) then b (r0 + n - 1) else b (r0 + n - 1) + 1"
          let ?bn = "if f (r0 + n) (b (r0 + n - 1)) < f (r0 + n) (b (r0 + n - 1) + 1) then b (r0 + n - 1) + 1 else b (r0 + n - 1)"
          let ?a = "a (r0 + n := ?an)"
          let ?b = "b (r0 + n := ?bn)"

          have "?a r0 = c0" "?b r0 = c0"
            using `n \<noteq> 0` `a r0 = c0` `b r0 = c0`
            by simp_all
            
          moreover

          have "\<forall>r. r0 \<le> r \<and> r < r0 + Suc n \<longrightarrow> f r (?b r) = (\<Sum> r' \<leftarrow> [r0..<r+1]. f r' (?a r'))"
          proof safe
            fix r
            assume "r0 \<le> r" "r < r0 + Suc n"
            show "f r (?b r) = (\<Sum> r' \<leftarrow> [r0..<r+1]. f r' (?a r'))"
            proof (cases "r < r0 + n")
              case True
              hence "f r (?b r) = (\<Sum> r' \<leftarrow> [r0..<r+1]. f r' (a r'))"
                using *(4) `r0 \<le> r`
                by simp
              also have "... = (\<Sum> r' \<leftarrow> [r0..<r+1]. f r' (?a r'))"
              proof (rule sum_list_cong, safe)
                fix r'
                assume "r' \<in> set [r0..<r + 1]"
                thus "f r' (a r') = f r' (?a r')"
                  using True `r0 \<le> r`
                  by auto
              qed
              finally show ?thesis
                by simp
            next
              case False
              hence "r = r0 + n"
                using `r < r0 + Suc n`
                by simp
              show ?thesis
              proof (cases "f (r0 + n) (b (r0 + n - 1)) < f (r0 + n) (b (r0 + n - 1) + 1)")
                case True
                have "f (r0 + n) (b (r0 + n - 1) + 1) = f (r0 + n - 1) (b (r0 + n - 1)) + f (r0 + n) (b (r0 + n - 1))"
                  using True ap
                  by simp
                hence "f (r0 + n) (b (r0 + n - 1) + 1) = ((\<Sum>r'\<leftarrow>[r0..<r0 + n]. f r' (a r'))) + f (r0 + n) (b (r0 + n - 1))"
                  using *(4) `n \<noteq> 0`
                  by simp
                also have "... = (\<Sum>r'\<leftarrow>[r0..<r0 + n]. f r' (if r' = r0 + n then b (r0 + n - 1) else (a r'))) + f (r0 + n) (if r0 + n = r0 + n then b (r0 + n - 1) else (a (r0 + n)))"
                proof-
                  have "(\<Sum>r'\<leftarrow>[r0..<r0 + n]. f r' (a r')) = (\<Sum>r'\<leftarrow>[r0..<r0 + n]. f r' (if r' = r0 + n then b (r0 + n - 1) else (a r')))"
                    by (rule sum_list_cong, simp)
                  thus ?thesis
                    by simp
                qed
                also have "... = (\<Sum>r'\<leftarrow>[r0..<r0 + n + 1]. f r' (if r' = r0 + n then b (r0 + n - 1) else (a r')))"
                  by (subst sum_list_last, simp_all)
                finally show ?thesis
                  using True `r = r0 + n` 
                  by simp (metis One_nat_def)
              next
                case False
                hence "f (r0 + n) (b (r0 + n - 1)) = f (r0 + n - 1) (b (r0 + n - 1)) + f (r0 + n) (b (r0 + n - 1) + 1)"
                  using ap
                  by simp
                hence "f (r0 + n) (b (r0 + n - 1)) = ((\<Sum>r'\<leftarrow>[r0..<r0 + n]. f r' (a r'))) + f (r0 + n) (b (r0 + n - 1) + 1)"
                  using *(4) `n \<noteq> 0`
                  by simp
                also have "... = (\<Sum>r'\<leftarrow>[r0..<r0 + n]. f r' (if r' = r0 + n then b (r0 + n - 1) + 1 else (a r'))) + f (r0 + n) (if r0 + n = r0 + n then b (r0 + n - 1) + 1 else (a (r0 + n)))"
                proof-
                  have "(\<Sum>r'\<leftarrow>[r0..<r0 + n]. f r' (a r')) = (\<Sum>r'\<leftarrow>[r0..<r0 + n]. f r' (if r' = r0 + n then b (r0 + n - 1) + 1 else (a r')))"
                    by (rule sum_list_cong, simp)
                  thus ?thesis
                    by simp
                qed
                also have "... = (\<Sum>r'\<leftarrow>[r0..<r0 + n + 1]. f r' (if r' = r0 + n then b (r0 + n - 1) + 1 else (a r')))"
                  by (subst sum_list_last, simp_all)
                finally
                show ?thesis
                  using False `r = r0 + n`
                  by simp (metis One_nat_def Suc_eq_plus1)
              qed
            qed
          qed

          moreover

          have "\<forall>r. r0 < r \<and> r < r0 + Suc n \<longrightarrow>
                    ?a r \<noteq> ?b r \<and>
                    c0 \<le> ?a r \<and> ?a r \<le> c0 + (r - r0) \<and>
                    c0 \<le> ?b r \<and> ?b r \<le> c0 + (r - r0) \<and>
                    (?a r = ?b (r - 1) \<or> ?a r = ?b (r - 1) + 1) \<and>
                    (?b r = ?b (r - 1) \<or> ?b r = ?b (r - 1) + 1)"
          proof safe
            fix r
            assume "r0 < r" "r < r0 + Suc n" "?a r = ?b r"
            then show False
              using *
              by (simp split: if_split_asm)
          next
            fix r
            assume "r0 < r" "r < r0 + Suc n"
            show "c0 \<le> ?a r"
            proof (cases "r < r0 + n")
              case True
              thus ?thesis
                using * `r0 < r`
                by auto
            next
              case False
              hence "r = r0 + n"
                using `r < r0 + Suc n`
                by simp
              thus ?thesis
                using *(2) *(3)[rule_format, of "r0 + n - 1"]
                by (smt Suc_diff_1 Suc_eq_plus1 Suc_leD Suc_le_mono \<open>r0 < r\<close> add_gr_0 diff_less fun_upd_same less_antisym less_or_eq_imp_le zero_less_one)
            qed
          next                
            fix r
            assume "r0 < r" "r < r0 + Suc n"
            show "?a r \<le> c0 + (r - r0)"
            proof (cases "r < r0 + n")
              case True
              thus ?thesis
                using * `r0 < r`
                by auto
            next
              case False
              hence "r = r0 + n"
                using `r < r0 + Suc n`
                by simp
              thus ?thesis
                using *(2) *(3)[rule_format, of "r0 + n - 1"]
                by (smt Suc_diff_Suc \<open>r0 < r\<close> add_Suc_right add_diff_cancel_left' add_diff_cancel_right' fun_upd_same le_Suc_eq less_Suc_eq less_or_eq_imp_le nat_add_left_cancel_le plus_1_eq_Suc)
            qed
          next
            fix r
            assume "r0 < r" "r < r0 + Suc n"
            show "c0 \<le> ?b r"
            proof (cases "r < r0 + n")
              case True
              thus ?thesis
                using * `r0 < r`
                by auto
            next
              case False
              hence "r = r0 + n"
                using `r < r0 + Suc n`
                by simp
              thus ?thesis
                using *(2) *(3)[rule_format, of "r0 + n - 1"]
                by (smt Suc_diff_1 Suc_eq_plus1 Suc_leD Suc_le_mono \<open>r0 < r\<close> add_gr_0 diff_less fun_upd_same less_antisym less_or_eq_imp_le zero_less_one)
            qed
          next
            fix r
            assume "r0 < r" "r < r0 + Suc n"
            show "?b r \<le> c0 + (r - r0)"
            proof (cases "r < r0 + n")
              case True
              thus ?thesis
                using * `r0 < r`
                by auto
            next
              case False
              hence "r = r0 + n"
                using `r < r0 + Suc n`
                by simp
              thus ?thesis
                using *(2) *(3)[rule_format, of "r0 + n - 1"]
                by (smt Suc_diff_Suc \<open>r0 < r\<close> add_Suc_right add_diff_cancel_left' add_diff_cancel_right' fun_upd_same le_Suc_eq less_Suc_eq less_or_eq_imp_le nat_add_left_cancel_le plus_1_eq_Suc)
            qed
          next
            fix r
            assume "r0 < r" "r < r0 + Suc n"
                   "?a r \<noteq> ?b (r - 1) + 1"
            then show "?a r = ?b (r - 1)"
              using *
              by (auto split: if_split_asm)
          next
            fix r
            assume "r0 < r" "r < r0 + Suc n"
                   "?b r \<noteq> ?b (r - 1) + 1"
            then show "?b r = ?b (r - 1)"
              using *
              by (auto split: if_split_asm)
          qed
          ultimately
          show ?thesis
            by blast
        qed
      qed
    qed
  qed

  obtain a b where *:
    "a 0 = 0" "b 0 = 0"
    "\<forall>r. 0 < r \<and> r < 2018 \<longrightarrow> a r \<noteq> b r"
    "\<forall>r. 0 < r \<and> r < 2018 \<longrightarrow> a r \<le> r"
    "\<forall>r. 0 < r \<and> r < 2018 \<longrightarrow> b r \<le> r"
    "\<forall>r. 0 < r \<and> r < 2018 \<longrightarrow> a r = b (r - 1) \<or> a r = b (r - 1) + 1"
    "\<forall>r. 0 < r \<and> r < 2018 \<longrightarrow> b r = b (r - 1) \<or> b r = b (r - 1) + 1"
    "\<forall>r<2018. f r (b r) = (\<Sum>r' \<leftarrow> [0..<r+1]. f r' (a r'))"
    using path[rule_format, of 0 0 2018]
    by auto

  have ab: "\<forall>r < 2018. a r = b r + 1 \<or> a r = b r - 1"
    using *(1-3) *(6-7)         
    by (metis Suc_eq_plus1 diff_add_inverse diff_is_0_eq' le0 neq0_conv plus_1_eq_Suc)
    
  have max_max: "\<forall>r. 0 < r \<and> r < 2018 \<longrightarrow> max (a (r - 1)) (b (r - 1)) \<le> max (a r) (b r)"
  proof safe
    fix r :: nat
    assume r: "0 < r" "r < 2018"
    show "max (a (r - 1)) (b (r - 1)) \<le> max (a r) (b r)"
    proof (cases "r = 1")
      case True
      thus ?thesis
        using `a 0 = 0` `b 0 = 0`
        by simp
    next
      case False
      then have "a r = b (r - 1) \<or> a r = b (r - 1) + 1"
                "b r = b (r - 1) \<or> b r = b (r - 1) + 1"
                "a r \<noteq> b r" "a (r - 1) \<noteq> b (r - 1)"
        using r * 
        by simp_all
      moreover
      have "a (r - 1) = b (r - 1) \<or> a (r - 1) = b (r - 1) + 1 \<or> a (r - 1) = b (r - 1) - 1"
        using ab[rule_format, of "r-1"] r False
        by auto
      ultimately
      show ?thesis
        by (smt diff_le_self eq_iff le_add1 max.commute max.mono)
    qed
  qed

  have min_min: "\<forall>r. 0 < r \<and> r < 2018 \<longrightarrow> min (a (r - 1)) (b (r - 1)) \<ge> min (a r) (b r) - 1"
    using "*"(2) "*"(3) "*"(6) "*"(7) 
    by (smt One_nat_def Suc_diff_Suc Suc_leD cancel_comm_monoid_add_class.diff_cancel diff_zero le_0_eq le_diff_conv less_Suc_eq min.cobounded1 min_def nat_less_le)

  let ?fa = "map (\<lambda> r. f r (a r)) [0..<2018]"

  have "inj_on (\<lambda> r. f r (a r)) (set [0..<2018])"
    unfolding inj_on_def
  proof safe
    fix r1 r2
    assume "r1 \<in> set [0..<2018]" "r2 \<in> set [0..<2018]"
      "f r1 (a r1) = f r2 (a r2)"
    have "(r1, a r1) \<in> triangle 0 0 2018" "(r2, a r2) \<in> triangle 0 0 2018"
      using `r1 \<in> set [0..<2018]` `r2 \<in> set [0..<2018]` *(4) *(1)
      using le_eq_less_or_eq triangle_def
      by auto
    moreover
    have "f r1 (a r1) = (uncurry f) (r1, a r1)"  "f r2 (a r2) = (uncurry f) (r2, a r2)"
      by auto
    ultimately
    show "r1 = r2"
      using `inj_on (uncurry f) (triangle 0 0 2018)` `f r1 (a r1) = f r2 (a r2)`
      by (metis inj_onD prod.inject)
  qed

  have "distinct ?fa"
    using `inj_on (\<lambda> r. f r (a r)) (set [0..<2018])`
    by (simp add: distinct_map)

  have "\<forall> x \<in> set ?fa. x > 0"
  proof safe
    fix x
    assume "x \<in> set ?fa"
    then obtain r where "r < 2018" "x = f r (a r)"
      by auto

    have "(r, a r) \<in> triangle 0 0 2018"
      using *(4) *(1) `r < 2018`
      by (cases "r = 0", auto simp add: triangle_def)
    moreover
    have "(uncurry f) (r, a r) = f r (a r)"
      by auto
    ultimately
    have "f r (a r) \<in> (uncurry f) ` triangle 0 0 2018"
      by (metis rev_image_eqI)
    then show "x > 0"
      using f(2) `x = f r (a r)`
      by auto
  qed

  have "set (map nat ?fa) = {1..<2018+1}"
  proof (rule consecutive_nats)
    show "length (map nat ?fa) = 2018"
      by simp
  next
    show "distinct (map nat ?fa)"
    proof (subst distinct_map, safe)
      show "distinct (map (\<lambda>r. f r (a r)) [0..<2018])"
        by fact
    next
      show "inj_on nat (set ?fa)"
        using `\<forall> x \<in> set ?fa. x > 0` inj_on_def
        by force
    qed
  next
    show "\<forall> x \<in> set (map nat ?fa). x > 0"
      using `\<forall> x \<in> set ?fa. x > 0`
      by simp
  next
    show "sum_list (map nat ?fa) \<le> 2018 * (2018 + 1) div 2"
    proof-
      have "(\<Sum> x \<leftarrow> ?fa. x) \<in> (uncurry f) ` (triangle 0 0 2018)"
      proof-
        have "(\<Sum> x \<leftarrow> ?fa. x) = f 2017 (b 2017)"
          using *(8)[rule_format, of 2017]
          by simp
        moreover
        have "(2017, b 2017) \<in> triangle 0 0 2018"
          using *(5)
          unfolding triangle_def
          by simp
        moreover
        have "(uncurry f) (2017, b 2017) = f 2017 (b 2017)"
          by simp
        ultimately
        show ?thesis
          by force
      qed
      hence "(\<Sum> x \<leftarrow> ?fa. x) \<le> 2018*(2018 + 1) div 2"
        using f(2)
        by auto
      moreover
      have "\<forall>x\<in>{0..<2018}. 0 \<le> f x (a x)"
        by (simp add: \<open>\<forall>x\<in>set (map (\<lambda>r. f r (a r)) [0..<2018]). 0 < x\<close> le_less)
      ultimately
      show ?thesis
        using sum_list_nat[of "[0..<2018]" "(\<lambda>r. f r (a r))"]
        by (simp add: comp_def)
    qed
  qed

  have "?fa <~~> map int [1..<2018+1]"
  proof-
    have "set ?fa = set (map int [1..<2018+1])"
    proof (subst inj_on_Un_image_eq_iff[symmetric])
      show "nat ` set ?fa = nat ` set (map int [1..<2018+1])"
      proof-
        have "set (map nat ?fa) = nat ` set ?fa"
          by auto
        moreover
        have "nat ` set (map int [1..<2018+1]) = {1..<2018+1}"
          by (metis (no_types, hide_lams) atLeastLessThan_upt map_idI map_map nat_int o_apply set_map)
        ultimately
        show ?thesis
          using `set (map nat ?fa) = {1..<2018+1}`
          by simp
      qed
    next
      show "inj_on nat (set ?fa \<union> set (map int [1..<2018 + 1]))"
      proof-
        have "set ?fa \<union> set (map int [1..<2018 + 1]) \<subseteq> {x::int. x > 0}"
          using `\<forall> x \<in> set ?fa. x > 0`
          by auto
        moreover
        have "inj_on nat {x::int. x > 0}"
          by (metis inj_on_inverseI mem_Collect_eq nat_int zero_less_imp_eq_int)
        ultimately
        show ?thesis
          by (smt inj_onD inj_onI subsetD)
      qed
    qed
    
    hence "mset ?fa = mset (map int [1..<2018+1])"
    proof (subst set_eq_iff_mset_eq_distinct[symmetric])
      show "distinct ?fa"
        by fact
    next 
      show "distinct (map int [1..<2018+1])"
        by (simp add: distinct_map)
    qed simp

    thus ?thesis
      using mset_eq_perm
      by blast
  qed

  let ?l = "min (a 2017) (b 2017)"
  let ?r = "max (a 2017) (b 2017)"
  let ?r0l = "2018 - ?l" and ?c0l = 0 and ?nl = "?l"
  let ?r0r = "?r + 1" and ?c0r = "?r + 1" and ?nr = "2017 - ?r"

  {
    fix r0 c0 n
    assume "triangle r0 c0 n \<subseteq> triangle 0 0 2018"
    assume "\<forall> r < 2018. (r, a r) \<notin> triangle r0 c0 n"
    assume "n \<ge> 1008"
    assume "c0 \<le> r0" "r0 + n \<le> 2018"

    have "\<forall> p \<in> triangle r0 c0 n. (uncurry f) p > 2018"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain r c where "(r, c) \<in> triangle r0 c0 n" "f r c \<le> 2018"
        by auto
      moreover
      have "(r, c) \<in> triangle 0 0 2018"
        using `triangle r0 c0 n \<subseteq> triangle 0 0 2018` `(r, c) \<in> triangle r0 c0 n`
        by auto
      then have "f r c \<ge> 1"
        using \<open>(uncurry f) ` (triangle 0 0 2018) = {1..<2018*(2018 + 1) div 2 + 1}\<close>
        by force
      then have "nat (f r c) \<in> {1..<2018+1}"
        using `f r c \<le> 2018`
        by auto      
      then have "f r c \<in> set (map int [1..<2018+1])"
        by (smt \<open>1 \<le> f r c\<close> atLeastLessThan_upt image_eqI int_nat_eq set_map)
      then have "f r c \<in> set ?fa"
        using `?fa <~~> map int [1..<2018+1]`
        using perm_set_eq
        by blast
      then obtain r' where "r' < 2018" "f r' (a r') = f r c"
        by auto
      have "(r', a r') \<in> triangle 0 0 2018"
        using `r' < 2018` *(1) *(4)
        by (cases "r' = 0") (auto simp add: triangle_def)
      hence "r = r'" "c = a r'"
        using `f r' (a r') = f r c` `inj_on (uncurry f) (triangle 0 0 2018)` `(r, c) \<in> triangle 0 0 2018`
        unfolding inj_on_def
        by force+

      then have "(r', a r') \<in> triangle r0 c0 n"
        using `(r, c) \<in> triangle r0 c0 n`
        by simp

      thus False
        using `r' < 2018` `\<forall> r < 2018. (r, a r) \<notin> triangle r0 c0 n`
        by auto
    qed

    obtain ar br where r:
      "ar r0 = c0" "br r0 = c0"
      "\<forall>r. r0 < r \<and> r < r0 + n \<longrightarrow> ar r \<noteq> br r \<and>
                     c0 \<le> ar r \<and> ar r \<le> c0 + (r - r0) \<and>
                     c0 \<le> br r \<and> br r \<le> c0 + (r - r0) \<and>
                     (ar r = br (r - 1) \<or> ar r = (br (r - 1)) + 1) \<and>
                     (br r = br (r - 1) \<or> br r = (br (r - 1)) + 1)"
      "\<forall>r. r0 \<le> r \<and> r < r0 + n \<longrightarrow>
                     f r (br r) =
                     (\<Sum>r'\<leftarrow>[r0..<r+1]. f r' (ar r'))"
      using `r0 + n \<le> 2018` `c0 \<le> r0` `n \<ge> 1008`
      using path[rule_format, of r0 c0 n]
      by auto

    have "\<forall> r. r0 \<le> r \<and> r < r0 + n \<longrightarrow> (r, ar r) \<in> triangle r0 c0 n"
    proof safe
      fix r
      assume "r0 \<le> r" "r < r0 + n" 
      then show "(r, ar r) \<in> triangle r0 c0 n"
        using r(1) r(2) r(3)[rule_format, of r]
        unfolding triangle_def
        by (cases "r = r0") auto
    qed
    then have "\<forall> r. r0 \<le> r \<and> r < r0 + n \<longrightarrow> f r (ar r) > 2018"
      using `\<forall> p \<in> triangle r0 c0 n. (uncurry f) p > 2018`
      by force

    have "(r0 + n - 1, br (r0 + n - 1)) \<in> triangle r0 c0 n"
      using r(3)[rule_format, of "r0 + n - 1"]
      using `r0 + n \<le> 2018` `n \<ge> 1008`
      by (simp add: triangle_def)
    hence "(r0 + n - 1, br (r0 + n - 1)) \<in> triangle 0 0 2018"
      using \<open>triangle r0 c0 n \<subseteq> triangle 0 0 2018\<close>
      by blast
    hence "(uncurry f) (r0 + n - 1, br (r0 + n - 1)) \<in> {1..<2018 * (2018 + 1) div 2 + 1}"
      using f(2)
      by blast
    hence "f (r0 + n - 1) (br (r0 + n - 1)) \<le> 2018*(2018+1) div 2"
      by simp

    moreover

    have "f (r0 + n - 1) (br (r0 + n - 1)) = (\<Sum>r'\<leftarrow>[r0..<(r0 + n - 1) + 1]. f r' (ar r'))"
      using r(4)[rule_format, of "r0 + n - 1"]
      using \<open>r0 + n \<le> 2018\<close> `n \<ge> 1008`
      by simp

    ultimately

    have 1: "(\<Sum>r'\<leftarrow>[r0..<(r0 + n - 1) + 1]. f r' (ar r')) \<le> 2018*(2018+1) div 2"
      by simp

    have "length ([r0..< (r0 + n - 1) + 1]) = n"
      using `n \<ge> 1008`
      by auto

    have "n * (2 * 2018 + n + 1) div 2 \<ge> 1008 * (2*2018 + 1008 + 1) div 2 "
    proof-
      have "n * (2 * 2018 + n + 1) \<ge> 1008 * (2*2018 + 1008 + 1)"
        using `n \<ge> 1008`
        by (metis Suc_eq_plus1 add_Suc mult_le_mono nat_add_left_cancel_le)
      thus ?thesis
        using div_le_mono
        by blast
    qed

    moreover

    have "length [r0..<(r0 + n - 1) + 1] * (2 * 2018 + length [r0..<(r0 + n - 1) + 1] + 1) div 2 \<le> 
          (\<Sum>r'\<leftarrow>[r0..<(r0 + n - 1) + 1]. nat (f r' (ar r')))"
    proof (rule sum_list_distinct_lb)
      have "\<forall>r'\<in>set [r0..<(r0 + n - 1) + 1]. 2018 < f r' (ar r')"
        using `\<forall> r. r0 \<le> r \<and> r < r0 + n \<longrightarrow> f r (ar r) > 2018` `n \<ge> 1008`
        by simp
      then show "\<forall>r'\<in>set [r0..<(r0 + n - 1)+ 1]. 2018 < nat (f r' (ar r'))"
        by auto
    next
      show "distinct (map (\<lambda>x. nat (f x (ar x))) [r0..<(r0 + n - 1) + 1])"
      proof (subst distinct_map, safe)
        show "inj_on (\<lambda>x. nat (f x (ar x))) (set [r0..<(r0 + n - 1) + 1])"
          unfolding inj_on_def
        proof safe
          fix r1 r2
          assume "r1 \<in> set [r0..<(r0 + n - 1) + 1]" "r2 \<in> set [r0..<(r0 + n - 1) + 1]"
                 "nat (f r1 (ar r1)) = nat (f r2 (ar r2))"
          have "(r1, ar r1) \<in> triangle r0 c0 n" "(r2, ar r2) \<in> triangle r0 c0 n"
            using `r1 \<in> set [r0..<(r0 + n - 1) + 1]` `r2 \<in> set [r0..<(r0 + n - 1) + 1]`
            using `\<forall> r. r0 \<le> r \<and> r < r0 + n \<longrightarrow> (r, ar r) \<in> triangle r0 c0 n`
            using `n \<ge> 1008`
            by force+

          then have "(r1, ar r1) \<in> triangle 0 0 2018" "(r2, ar r2) \<in> triangle 0 0 2018"
            using \<open>triangle r0 c0 n \<subseteq> triangle 0 0 2018\<close>
            by blast+

          moreover

          have "f r1 (a r1) = (uncurry f) (r1, a r1)"  "f r2 (a r2) = (uncurry f) (r2, a r2)"
            by auto

          moreover

          have "f r1 (a r1) = f r2 (a r2)"
            using `(r1, ar r1) \<in> triangle 0 0 2018` `(r2, ar r2) \<in> triangle 0 0 2018`
            using `nat (f r1 (ar r1)) = nat (f r2 (ar r2))`
            using \<open>(r1, ar r1) \<in> triangle r0 c0 n\<close> 
            using \<open>\<forall> p \<in> triangle r0 c0 n. 2018 < uncurry f p\<close>
            using \<open>inj_on (uncurry f) (triangle 0 0 2018)\<close> 
            by (smt Pair_inject eq_nat_nat_iff inj_on_def nat_0_iff uncurry.simps)

          ultimately

          show "r1 = r2"
            using `inj_on (uncurry f) (triangle 0 0 2018)`
            using \<open>(r1, ar r1) \<in> triangle r0 c0 n\<close>
                  \<open>\<forall>p\<in>triangle r0 c0 n. 2018 < uncurry f p\<close>
                  \<open>nat (f r1 (ar r1)) = nat (f r2 (ar r2))\<close>
            by (smt Pair_inject inj_on_eq_iff int_nat_eq uncurry.simps) 
        qed
      qed simp
    qed

    ultimately

    have "(\<Sum>r'\<leftarrow>[r0..<(r0 + n - 1) + 1]. nat (f r' (ar r'))) \<ge> 1008 * (2*2018 + 1008 + 1) div 2"
      using `length ([r0..< (r0 + n - 1) + 1]) = n`
      by simp

    moreover

    have "(\<Sum>r'\<leftarrow>[r0..<(r0 + n - 1) + 1]. nat (f r' (ar r'))) = nat ((\<Sum>r'\<leftarrow>[r0..<(r0 + n - 1) + 1]. f r' (ar r')))"
    proof (rule sum_list_nat)
      show "\<forall>r'\<in>set [r0..<(r0 + n - 1) + 1]. 0 \<le> f r' (ar r')"
        using `\<forall> r. r0 \<le> r \<and> r < r0 + n \<longrightarrow> f r (ar r) > 2018` `n \<ge> 1008`
        by auto
    qed

    ultimately

    have 2: "nat ((\<Sum>r'\<leftarrow>[r0..<(r0 + n - 1) + 1]. f r' (ar r'))) \<ge> 1008 * (2*2018 + 1008 + 1) div 2"
      by simp
      

    have False
      using 1 2
      by simp
  } note triangle = this

  show False
  proof (cases "?nl \<le> ?nr")
    case True
    show False
    proof (rule triangle)
      show "triangle ?r0r ?c0r ?nr \<subseteq> triangle 0 0 2018"
        unfolding triangle_def
        by auto
    next
      show "?nr \<ge> 1008"
        using ab[rule_format, of 2017] True
        by (auto simp add: max_def min_def split: if_split_asm)
    next
      show "\<forall> r < 2018. (r, a r) \<notin> triangle ?r0r ?c0r ?nr"
      proof-
        have "\<forall> r < 2018. max (a r) (b r) \<le> ?r"
        proof-
          have "\<forall> r < 2018. max (a (2017 - r)) (b (2017 - r)) \<le> ?r"
          proof safe
            fix r::nat
            assume "r < 2018"
            then show "max (a (2017 - r)) (b (2017 - r)) \<le> ?r"
            proof (induction r)
              case 0
              thus ?case
                by simp
            next
              case (Suc r)
              thus ?case
                using max_max *(1-2)
                by (smt Suc_diff_Suc Suc_lessD add_diff_cancel_left' diff_Suc_Suc diff_less_Suc max.boundedE max.orderE one_plus_numeral plus_1_eq_Suc semiring_norm(4) semiring_norm(5) zero_less_diff)
            qed
          qed
          thus ?thesis
            by (metis Suc_leI add_le_cancel_left diff_diff_cancel diff_less_Suc one_plus_numeral plus_1_eq_Suc semiring_norm(4) semiring_norm(5))
        qed
        thus ?thesis
          unfolding triangle_def
          by auto
      qed
    next
      show "?r0r \<le> ?c0r"
        by simp
    next
      show "?r0r + ?nr \<le> 2018"
        by (simp add: "*"(4) "*"(5))
    qed
  next
    case False
    show ?thesis
    proof (rule triangle)
      show "triangle ?r0l ?c0l ?nl \<subseteq> triangle 0 0 2018"
        using *(4)[rule_format, of 2017] *(5)[rule_format, of 2017]
        unfolding triangle_def
        by auto
    next
      show "?c0l \<le> ?r0l"
        by simp
    next
      show "2018 - min (a 2017) (b 2017) + min (a 2017) (b 2017) \<le> 2018"
        using *(4)[rule_format, of 2017] *(5)[rule_format, of 2017]
        by auto
    next
      show "?nl \<ge> 1008"
        using ab[rule_format, of 2017] False
        by (auto simp add: max_def min_def split: if_split_asm)
    next
      show "\<forall> r < 2018. (r, a r) \<notin> triangle ?r0l ?c0l ?nl"
      proof-
        have "\<forall> r < 2018. min (a r) (b r) \<ge> ?l - (2017 - r)"
        proof-
          have "\<forall> r < 2018. min (a (2017 - r)) (b (2017 - r)) \<ge> ?l - (2017 - (2017 - r))"
          proof safe
            fix r::nat
            assume "r < 2018"
            then show "?l - (2017 - (2017 - r)) \<le> min (a (2017 - r)) (b (2017 - r))"
            proof (induction r)
              case 0
              thus ?case
                by simp
            next
              case (Suc r)
              have "min (a 2017) (b 2017) - (2017 - (2017 - Suc r)) = min (a 2017) (b 2017) - r - 1"
                using `Suc r < 2018`
                by auto
              also have "... \<le>  min (a (2017 - r)) (b (2017 - r)) - 1"
                using Suc
                by (smt Suc_lessD diff_Suc_Suc diff_diff_cancel diff_le_mono le_less one_plus_numeral plus_1_eq_Suc semiring_norm(4) semiring_norm(5) zero_less_diff)
              also have "... \<le> min (a (2017 - r - 1)) (b (2017 - r - 1))"
                using min_min[rule_format, of "2017 - r"] `Suc r < 2018`
                by simp
              finally
              show ?case
                by simp
            qed
          qed
          thus ?thesis
            by (smt diff_diff_cancel diff_less_Suc le_less less_Suc_eq one_plus_numeral plus_1_eq_Suc semiring_norm(4) semiring_norm(5))
        qed
        thus ?thesis
          by (auto simp add: triangle_def)
      qed
    qed
  qed
qed

end                                                         