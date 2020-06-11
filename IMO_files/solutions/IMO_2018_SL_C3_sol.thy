subsection \<open>IMO 2018 SL - C3\<close>

theory IMO_2018_SL_C3_sol
  imports Complex_Main
begin

subsubsection \<open>General lemmas\<close>

lemma sum_list_int [simp]:
  fixes xs :: "nat list"
  shows "(\<Sum> x \<leftarrow> xs. int (f x)) = int (\<Sum> x \<leftarrow> xs. f x)"
  by (induction xs, auto)

lemma sum_list_comp:
  shows "(\<Sum> x \<leftarrow> xs. f (g x)) = (\<Sum> x \<leftarrow> map g xs. f x)"
  by (induction xs, auto)

lemma lt_ceiling_frac:
  assumes "x < ceiling (a / b)" "b > 0"
  shows "x * b < a"
  using assms
  by (metis (no_types, hide_lams) floor_less_iff floor_uminus_of_int less_ceiling_iff minus_mult_minus mult_minus_right of_int_0_less_iff of_int_minus of_int_mult pos_less_divide_eq)

lemma subset_Max:
  fixes X :: "nat set"
  assumes "finite X"
  shows "X \<subseteq> {0..<Max X + 1}"
  using assms
  by (induction X rule: finite.induct) (auto simp add: less_Suc_eq_le subsetI)

lemma card_Max:
  fixes X :: "nat set"
  shows "card X \<le> Max X + 1"
proof (cases "finite X")
  case True
  then show ?thesis
    using subset_Max[of X]
    using subset_eq_atLeast0_lessThan_card by blast
next
  case False
  then show ?thesis
    by simp
qed

lemma sum_length_parts:
  assumes "\<forall> i j. i < j \<and> j < length ps \<longrightarrow> set (filter (ps ! i) xs) \<inter> set (filter (ps ! j) xs) = {}"
  shows "sum_list (map (\<lambda> p. length (filter p xs)) ps) \<le> length xs"
  using assms
proof (induction ps arbitrary: xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ps)
  let ?xs' = "filter (\<lambda> x. \<not> p x) xs"
  have "(\<Sum>p\<leftarrow>ps. length (filter p xs)) = (\<Sum>p\<leftarrow>ps. length (filter p ?xs'))"
  proof-
    have *: "\<forall> p' \<in> set ps. set (filter p xs) \<inter> set (filter p' xs) = {}"
      using Cons(2)[rule_format, of 0]
      by (metis Suc_less_eq in_set_conv_nth length_Cons list.sel(3) nth_Cons_0 nth_tl zero_less_Suc)
    have "\<forall> p \<in> set ps. filter p xs = filter p ?xs'"
    proof
      fix p'
      assume "p' \<in> set ps"
      then have "set (filter p xs) \<inter> set (filter p' xs) = {}"
        using *
        by auto
      show "filter p' xs = filter p' ?xs'"
      proof (subst filter_filter, rule filter_cong)
        fix x
        assume "x \<in> set xs"
        then show "p' x = (\<not> p x \<and> p' x)"
          using \<open>set (filter p xs) \<inter> set (filter p' xs) = {}\<close>
          by auto
      qed simp
    qed
    then have "\<forall> p \<in> set ps. length (filter p xs) = length (filter p ?xs')"
      by simp
    then show ?thesis
      by (metis (no_types, lifting) map_eq_conv)
  qed
  moreover
  have "(\<Sum>pa\<leftarrow>ps. length (filter pa (filter (\<lambda>x. \<not> p x) xs))) \<le> length (filter (\<lambda>x. \<not> p x) xs)"
  proof (rule Cons(1), safe)
    fix i j x
    assume "i < j" "j < length ps" "x \<in> set (filter (ps ! i) ?xs')"  "x \<in> set (filter (ps ! j) ?xs')"
    then have False
      using Cons(2)[rule_format, of "i+1" "j+1"]
      by auto
    then show "x \<in> {}"
      by simp
  qed

  moreover
  have "length (filter p xs) + length (filter (\<lambda> x. \<not> p x) xs) = length xs"
    using sum_length_filter_compl
    by blast

  ultimately

  show ?case
    by simp
qed


lemma hd_filter:
  assumes "filter P xs \<noteq> []"
  shows "\<exists> k. k < length xs \<and> (filter P xs) ! 0 = xs ! k \<and> P (xs ! k) \<and> (\<forall> k' < k. \<not> P (xs ! k'))"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "P x")
    case True
    then show ?thesis
      by auto
  next
    case False
    then obtain k where "k<length xs" "filter P xs ! 0 = xs ! k" "P (xs ! k)" "(\<forall>k'<k. \<not> P (xs ! k'))"
      using Cons
      by auto
    then show ?thesis
      using False
      by (rule_tac x="k+1" in exI, simp add: nth_Cons')
  qed
qed

lemma last_filter:
  assumes "filter P xs \<noteq> []"
  shows "\<exists> k. k < length xs \<and> (filter P xs) ! (length (filter P xs) - 1) = xs ! k \<and> P (xs ! k) \<and> (\<forall> k'. k < k' \<and> k' < length xs \<longrightarrow> \<not> P (xs ! k'))"
proof-
  have "filter P (rev xs) \<noteq> []"
    using assms
    by (metis Nil_is_rev_conv rev_filter)
  then obtain k where *: "k < length xs" "filter P (rev xs) ! 0 = rev xs ! k" "P (rev xs ! k)" "\<forall> k' < k. \<not> P (rev xs ! k')"
    using hd_filter[of P "rev xs"]
    by auto
  show ?thesis
  proof (rule_tac x="length xs - (k + 1)" in exI, safe)
    show "length xs - (k + 1) < length xs"
      using *(1)
      by simp
  next
    show "filter P xs ! (length (filter P xs) - 1) = xs ! (length xs - (k + 1))"
      using *(1) *(2)
      by (metis One_nat_def add.right_neutral add_Suc_right assms length_greater_0_conv rev_filter rev_nth)
  next
    show "P (xs ! (length xs - (k + 1)))"
      using *(1) *(3)
      by (simp add: rev_nth)
  next
    fix k'
    assume "length xs - (k + 1) < k'" "k' < length xs" "P (xs ! k')"
    then show False
      using *(1) *(4)[rule_format, of "length xs - (k' + 1)"]
      by (smt add.commute add_diff_cancel_right add_diff_cancel_right' add_diff_inverse_nat add_gr_0 diff_less diff_less_mono2 not_less_eq plus_1_eq_Suc rev_nth zero_less_one)
  qed    
qed

lemma filter_tl [simp]:
  "filter P (tl xs) = (if P (hd xs) then tl (filter P xs) else filter P xs)"
  by (smt filter.simps(1) filter.simps(2) filter_empty_conv hd_Cons_tl hd_in_set list.inject list.sel(2))

lemma filter_dropWhile_not [simp]:
  shows "filter P (dropWhile (\<lambda>x. \<not> P x) xs) = filter P xs"
  by (metis (no_types, lifting) filter_False filter_append self_append_conv2 set_takeWhileD takeWhile_dropWhile_id)

lemma inside_filter:
  assumes "i + 1 < length (filter P xs)"
  shows "\<exists> k1 k2. k1 < k2 \<and> k2 < length xs \<and> 
                  (filter P xs) ! i = xs ! k1 \<and> 
                  (filter P xs) ! (i + 1) = xs ! k2 \<and> 
                  P (xs ! k1) \<and> P (xs ! k2) \<and> 
                  (\<forall> k'. k1 < k' \<and> k' < k2 \<longrightarrow> \<not> P (xs ! k'))"
  using assms
proof (induction i arbitrary: xs)
  case 0
  then obtain k1 where "k1 < length xs" "filter P xs ! 0 = xs ! k1" "P (xs ! k1)" "\<forall> k' < k1. \<not> P (xs ! k')"
    using hd_filter
    by (metis gr_implies_not_zero length_0_conv)
  let ?xs = "drop (k1 + 1) xs"
  have "filter P (take (k1 + 1) xs) = [xs ! k1]"
  proof-
    have "filter P (take k1 xs) = []"
      using \<open>\<forall> k' < k1. \<not> P (xs ! k')\<close> \<open>k1 < length xs\<close>
      using last_filter
      by force
    moreover
    have "take (k1 + 1) xs = take k1 xs @ [xs ! k1]"
      using \<open>k1 < length xs\<close>
      using take_Suc_conv_app_nth
      by auto
    ultimately 
    show ?thesis
      using \<open>P (xs ! k1)\<close>
      by simp
  qed
  then have "filter P ?xs \<noteq> []"
    using 0
    by (metis One_nat_def Suc_eq_plus1 append_take_drop_id filter_append length_Cons length_append less_not_refl3 list.size(3) plus_1_eq_Suc)
  then obtain k2' where *: "k2' < length ?xs" "filter P ?xs ! 0 = ?xs ! k2'" "P (?xs ! k2')" "\<forall> k' < k2'. \<not> P (?xs ! k')"
    using hd_filter[of P ?xs]
    by auto
  have "filter P xs ! 1 = xs ! (k1 + 1 + k2')"
    using * \<open>filter P (take (k1 + 1) xs) = [xs ! k1]\<close> \<open>k1 < length xs\<close>
    by (metis One_nat_def Suc_eq_plus1 Suc_leI append_take_drop_id filter_append length_Cons list.size(3) nth_append_length_plus nth_drop plus_1_eq_Suc)
  moreover
  have "P (xs ! (k1 + 1 + k2'))"
    using * \<open>k1 < length xs\<close>
    by auto
  moreover
  have "\<forall> k'. k1 < k' \<and> k' < k1 + 1 + k2' \<longrightarrow> \<not> P (xs ! k')"
  proof safe
    fix k'
    assume "k1 < k'" "k' < k1 + 1 + k2'" "P (xs ! k')"
    then have "k' - (k1 + 1) < k2'"
      by auto
    then have "\<not> P (?xs ! (k' - (k1 + 1)))"
      using \<open>\<forall> k' < k2'. \<not> P (?xs ! k')\<close>
      by simp
    then have "\<not> P (xs ! k')"
      using \<open>k2' < length ?xs\<close>
      using \<open>k1 < k'\<close>
      by auto
    then show False
      using \<open>P (xs ! k')\<close>
      by simp
  qed
  moreover
  have "k1 + 1 + k2' < length xs"
    using \<open>k2' < length ?xs\<close>
    by auto
  ultimately
  show ?case
    using \<open>P (xs ! k1)\<close> \<open>filter P xs ! 0 = xs ! k1\<close>
    by (rule_tac x=k1 in exI, rule_tac x="k1+1+k2'" in exI, simp)
next
  case (Suc i)
  let ?t = "takeWhile (\<lambda> x. \<not> P x) xs" and ?d = "dropWhile (\<lambda> x. \<not> P x) xs"
  let ?xs = "tl ?d"

  have "?xs \<noteq> []"
    using Suc(2)
    by (metis Suc_eq_plus1 add.commute add_less_cancel_left filter.simps(1) filter_dropWhile_not filter_tl hd_Cons_tl length_Cons list.size(3) not_less_zero)

  have *: "\<forall> k. length ?t + k + 1 < length xs \<longrightarrow> xs ! (length ?t + k + 1) = tl ?d ! k"
    by (metis One_nat_def add.right_neutral add_Suc_right add_lessD1 hd_Cons_tl length_append less_le list.size(3) nth_Cons_Suc nth_append_length_plus takeWhile_dropWhile_id)

  have "i + 1 < length (filter P ?xs)"
    using Suc(2)
    by auto
  then obtain k1 k2
    where "k1 < k2" "k2 < length ?xs"
       "filter P ?xs ! i = ?xs ! k1"
       "filter P ?xs ! (i + 1) = ?xs ! k2"
       "P (?xs ! k1)"
       "P (?xs ! k2)" 
       "\<forall>k'. k1 < k' \<and> k' < k2 \<longrightarrow> \<not> P (?xs ! k')"
    using Suc(1)[of ?xs]
    by auto
  show ?case
  proof (rule_tac x="k1+length ?t+1" in exI, rule_tac x="k2+length ?t+1" in exI, safe)
    show "k1 + length ?t + 1 < k2 + length ?t + 1"
      using \<open>k1 < k2\<close>
      by simp
  next
    have "k2 + length ?t + 1 < length ?xs + 1 + length ?t"
      using \<open>k2 < length ?xs\<close>
      by simp
    then show "k2 + length ?t + 1 < length xs"
      using \<open>?xs \<noteq> []\<close>
      by (metis One_nat_def Suc_eq_plus1 Suc_pred add.commute add_lessD1 length_append length_greater_0_conv length_tl less_diff_conv takeWhile_dropWhile_id)
  next
    show "P (xs ! (k1 + length ?t + 1))"
      using \<open>P (?xs ! k1)\<close> \<open>k1 < k2\<close> \<open>k2 < length ?xs\<close> *
      by (metis Suc_eq_plus1 add.commute add_Suc_right hd_Cons_tl length_greater_0_conv length_tl list.size(3) not_less_zero nth_Cons_Suc nth_append_length_plus takeWhile_dropWhile_id zero_less_diff)
  next
    show "P (xs ! (k2 + length (takeWhile (\<lambda>x. \<not> P x) xs) + 1))"
      using \<open>P (?xs ! k2)\<close> \<open>k2 < length ?xs\<close> *
      by (metis Suc_eq_plus1 add.commute add_Suc_right hd_Cons_tl length_greater_0_conv length_tl list.size(3) not_less_zero nth_Cons_Suc nth_append_length_plus takeWhile_dropWhile_id zero_less_diff)
  next
    fix k'
    assume "k1 + length ?t + 1 < k'" "k' < k2 + length ?t + 1" "P (xs ! k')"
    then have "k1 < k' - (length ?t + 1)" "k' - (length ?t + 1) < k2"
      using \<open>k1 < k2\<close> \<open>k2 < length ?xs\<close>
      by linarith+
    moreover
    have "length ?t + (k' - (length ?t + 1)) + 1 < length xs"
      using \<open>k2 < length (tl (dropWhile (\<lambda>x. \<not> P x) xs))\<close>
      by (smt  ab_semigroup_add_class.add_ac(1) add.commute add_lessD1 add_less_cancel_left calculation(2) length_append length_tl less_diff_conv less_trans_Suc plus_1_eq_Suc takeWhile_dropWhile_id)
    then have "P (?xs ! (k' - (length ?t + 1)))"
      using *[rule_format, of "k' - (length ?t + 1)"] \<open>P (xs ! k')\<close>
      by (metis Suc_eq_plus1 add_Suc add_diff_inverse_nat calculation(1) nat_diff_split not_less_zero)
    ultimately
    show False
      using \<open>\<forall>k'. k1 < k' \<and> k' < k2 \<longrightarrow> \<not> P (?xs ! k')\<close>[rule_format, of "k' - (length ?t + 1)"] \<open>k1 < k2\<close> \<open>k2 < length ?xs\<close>
      by simp
  next
    show "filter P xs ! (Suc i) = xs ! (k1 + length ?t + 1)"
    proof-
      have "filter P xs ! (Suc i) = filter P ?d ! (Suc i)"
        by simp
      also have "... = filter P (tl ?d) ! i"
        using \<open>?xs \<noteq> []\<close> \<open>i + 1 < length (filter P ?xs)\<close>
        by (metis  add_lessD1 filter_tl hd_dropWhile list.sel(2) nth_tl)
      finally
      show ?thesis
        using \<open>filter P ?xs ! i = ?xs ! k1\<close> *
        using \<open>k1 < k2\<close> \<open>k2 < length ?xs\<close> 
        by (smt Suc_eq_plus1 add.commute add_Suc_right add_lessD1 add_less_cancel_left length_append length_tl less_diff_conv less_trans_Suc takeWhile_dropWhile_id)
    qed
  next
    show "filter P xs ! (Suc i + 1) = xs ! (k2 + length ?t + 1)"
    proof-
      have "filter P xs ! (Suc i + 1) = filter P ?d ! (Suc i + 1)"
        by simp
      also have "... = filter P (tl ?d) ! (Suc i)"
        using \<open>?xs \<noteq> []\<close> \<open>i + 1 < length (filter P ?xs)\<close>
        by (metis add.commute filter_tl hd_dropWhile nth_tl plus_1_eq_Suc tl_Nil)
      finally
      show ?thesis
        using \<open>filter P ?xs ! (i + 1) = ?xs ! k2\<close> *
        using \<open>k1 < k2\<close> \<open>k2 < length ?xs\<close> 
        by (smt Suc_eq_plus1 add.commute add_Suc_right add_lessD1 add_less_cancel_left length_append length_tl less_diff_conv less_trans_Suc takeWhile_dropWhile_id)
    qed
  qed
qed


subsubsection \<open>Unlabeled states\<close>

type_synonym state = "nat list"

definition initial_state :: "nat \<Rightarrow> state" where
  "initial_state n = (replicate (n + 1) 0) [0 := n]"

definition final_state :: "nat \<Rightarrow> state" where
  "final_state n = (replicate (n + 1) 0) [n := n]"

definition valid_state :: "nat \<Rightarrow> state \<Rightarrow> bool" where
   "valid_state n state \<longleftrightarrow> length state = n + 1 \<and> sum_list state = n"

definition move :: "nat \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" where
  "move p1 p2 state = 
     (let k1 = state ! p1;                     
          k2 = state ! p2
       in state [p1 := k1 - 1, p2 := k2 + 1])"

definition valid_move' :: "nat  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where 
  "valid_move' n p1 p2 state state' \<longleftrightarrow> 
      (let k1 = state ! p1
        in k1 > 0 \<and> p1 < p2 \<and> p2 \<le> p1 + k1 \<and> p2 \<le> n \<and>
           state' = move p1 p2 state)"

definition valid_move :: "nat \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where 
  "valid_move n state state' \<longleftrightarrow> 
      (\<exists> p1 p2. valid_move' n p1 p2 state state')"

definition valid_moves where
  "valid_moves n states \<longleftrightarrow> 
      (\<forall> i < length states - 1. valid_move n (states ! i) (states ! (i + 1)))"

definition valid_game where
  "valid_game n states \<longleftrightarrow> 
       length states \<ge> 2 \<and>
       hd states = initial_state n \<and> 
       last states = final_state n \<and> 
       valid_moves n states"


lemma valid_state_initial_state [simp]:
  shows "valid_state n (initial_state n)"
  by (simp add: initial_state_def valid_state_def)

lemma valid_move_valid_state:
  assumes "valid_state n state" "valid_move n state state'"
  shows "valid_state n state'"
proof-
  obtain p1 p2
    where *: "0 < state ! p1" "p1 < p2" "p2 \<le> p1 + state ! p1" "p2 \<le> n" "state' = state[p1 := state ! p1 - 1, p2 := state ! p2 + 1]"
    using assms
    unfolding valid_move_def valid_move'_def move_def Let_def
    by auto
  then have "sum_list state > 0"
    using assms(1) valid_state_def
    by auto
  then have "sum_list (state[p1 := state ! p1 - 1, p2 := state ! p2 + 1]) = sum_list state"
    using * assms
    using sum_list_update[of p1 state "state ! p1 - 1"]
    using sum_list_update[of p2 "state[p1 := state ! p1 - 1]" "state ! p2 + 1"]
    unfolding valid_state_def
    by auto
  then show ?thesis
    using \<open>valid_state n state\<close> *
    by (simp add: valid_state_def)
qed

lemma valid_moves_Nil [simp]:
  shows "valid_moves n []"
  by (simp add: valid_moves_def)

lemma valid_moves_Single [simp]:
  shows "valid_moves n [state]"
  by (simp add: valid_moves_def)

lemma valid_moves_Cons [simp]:
  shows "valid_moves n (state1 # state2 # states) \<longleftrightarrow> 
         valid_move n state1 state2 \<and> valid_moves n (state2 # states)"
  unfolding valid_moves_def
  by (auto simp add: nth_Cons split: nat.split)

lemma valid_moves_valid_states:
  assumes "valid_moves n states" "valid_state n (hd states)"
  shows "\<forall> state \<in> set states. valid_state n state"
  using assms
proof (induction states)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a states)
  then show ?case
    by (metis list.sel(1) list.set_cases set_ConsD valid_moves_Cons valid_move_valid_state)
qed

lemma valid_game_valid_states:
  assumes "valid_game n states"
  shows "\<forall> state \<in> set states. valid_state n state"
  using assms
  unfolding valid_game_def
  using valid_moves_valid_states
  by fastforce

definition move_positions where
  "move_positions state state' = 
    (THE (p1, p2). valid_move' (length state - 1) p1 p2 state state')"

lemma move_positions_unique:
  assumes "valid_state n state" "valid_move n state state'"
  shows "\<exists>! (p1, p2). valid_move' n p1 p2 state state'"
proof-
  have "length state = n + 1"
    using assms
    unfolding valid_state_def
    by simp

  have "\<exists>! p1. p1 < length state \<and> state ! p1 > 0 \<and> state' ! p1 = state ! p1 - 1"
    using assms
    unfolding valid_state_def valid_move_def valid_move'_def Let_def move_def
    by (smt add.right_neutral add_Suc_right add_diff_cancel_left' le_SucI less_imp_Suc_add less_le_trans list_update_swap n_not_Suc_n nat.simps(3) nth_list_update_eq nth_list_update_neq plus_1_eq_Suc)
  then have *: "\<exists>! p1. p1 \<le> n \<and> state ! p1 > 0 \<and> state' ! p1 = state ! p1 - 1"
    using \<open>length state = n + 1\<close>
    by (metis Nat.le_diff_conv2 Suc_leI add.commute add_diff_cancel_right' le_add2 le_imp_less_Suc plus_1_eq_Suc)

  have "\<exists>! p2. p2 < length state \<and> state' ! p2 = state ! p2 + 1"
    using assms
    unfolding valid_state_def valid_move_def valid_move'_def Let_def move_def
    by (metis Groups.add_ac(2) diff_le_self le_imp_less_Suc length_list_update n_not_Suc_n nat_neq_iff nth_list_update_eq nth_list_update_neq plus_1_eq_Suc)
  then have **: "\<exists>! p2. p2 \<le> n \<and> state' ! p2 = state ! p2 + 1"
    using \<open>length state = n + 1\<close>
    by (simp add: discrete)

  obtain p1 p2 where "valid_move' n p1 p2 state state'"
    using assms
    unfolding valid_move_def
    by auto
  show ?thesis
  proof
    show "case (p1, p2) of (p1, p2) \<Rightarrow> valid_move' n p1 p2 state state'"
      using \<open>valid_move' n p1 p2 state state'\<close>
      by simp
  next
    fix x
    assume "case x of (p1', p2') \<Rightarrow> valid_move' n p1' p2' state state'"
    then obtain p1' p2' where "x = (p1', p2')" "valid_move' n p1' p2' state state'"
      by auto
    then show "x = (p1, p2)"
      using \<open>valid_move' n p1 p2 state state'\<close> * **  \<open>length state = n + 1\<close>
      unfolding valid_move'_def move_def Let_def
      by (metis Nat.add_0_right One_nat_def add_Suc_right le_imp_less_Suc le_less_trans length_list_update less_imp_le_nat nat_neq_iff nth_list_update_eq nth_list_update_neq)
  qed
qed

lemma valid_move'_move_positions:
  assumes "valid_state n state" "valid_move' n p1 p2 state state'"
  shows "(p1, p2) = move_positions state state'"
proof-
  have *: "(THE x. let (p1', p2') = x in valid_move' (length state - 1) p1' p2' state state') = (p1, p2)"
  proof (rule the_equality)
    show "let (p1', p2') = (p1, p2) in valid_move' (length state - 1) p1' p2' state state'"
      using assms
      unfolding valid_state_def valid_move_def Let_def
      by auto
  next
    fix x
    assume "let (p1', p2') = x in valid_move' (length state - 1) p1' p2' state state'"
    then show "x = (p1, p2)"
      using move_positions_unique[of n state state'] assms
      unfolding valid_state_def valid_move_def
      by auto
  qed
  then show ?thesis
    unfolding move_positions_def Let_def
    by auto
qed

lemma move_positions_valid_move':
  assumes "valid_state n state" "valid_move n state state'"
          "(p1, p2) = move_positions state state'"
  shows "valid_move' n p1 p2 state state'"
  using assms
  by (metis fstI sndI valid_move_def valid_move'_move_positions)

subsubsection \<open>Labeled states\<close>

type_synonym labeled_state = "(nat set) list"

definition initial_labeled_state :: "nat \<Rightarrow> labeled_state" where
  "initial_labeled_state n  = (replicate (n+1) {}) [0 := {0..<n}]"

definition final_labeled_state :: "nat \<Rightarrow> labeled_state" where
  "final_labeled_state n  = (replicate (n+1) {}) [n := {0..<n}]"

definition valid_labeled_state :: "nat \<Rightarrow> labeled_state \<Rightarrow> bool" where
  "valid_labeled_state n l_state \<longleftrightarrow> 
        length l_state = n+1 \<and>
        (\<forall> i j. i < j \<and> j \<le> n \<longrightarrow> l_state ! i \<inter> l_state ! j = {}) \<and>
        (\<Union> (set l_state)) = {0..<n}"

definition labeled_move where 
  "labeled_move p1 p2 stone l_state = 
    (let ss1 = l_state ! p1;
         ss2 = l_state ! p2 
      in l_state [p1 := ss1 - {stone}, p2 := ss2 \<union> {stone}])"

definition valid_labeled_move' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> labeled_state \<Rightarrow> labeled_state \<Rightarrow> bool" where 
  "valid_labeled_move' n p1 p2 stone l_state l_state' \<longleftrightarrow> 
      (let ss1 = l_state ! p1
        in p1 < p2 \<and> p2 \<le> p1 + card ss1 \<and> p2 \<le> n \<and>
           stone \<in> ss1 \<and> l_state' = labeled_move p1 p2 stone l_state)"

definition valid_labeled_move :: "nat \<Rightarrow> labeled_state \<Rightarrow> labeled_state \<Rightarrow> bool" where 
  "valid_labeled_move n l_state l_state' \<longleftrightarrow> 
      (\<exists> p1 p2 stone. valid_labeled_move' n p1 p2 stone l_state l_state')"

definition valid_labeled_moves where
  "valid_labeled_moves n l_states \<longleftrightarrow> 
     (\<forall> i < length l_states - 1. valid_labeled_move n (l_states ! i) (l_states ! (i + 1)))"

definition valid_labeled_game where
  "valid_labeled_game n l_states \<longleftrightarrow> 
       length l_states \<ge> 2 \<and>
       hd l_states = initial_labeled_state n \<and> 
       last l_states = final_labeled_state n \<and> 
       valid_labeled_moves n l_states"

lemma valid_labeled_state_initial_labeled_state [simp]:
  shows "valid_labeled_state n (initial_labeled_state n)"
  unfolding valid_labeled_state_def initial_labeled_state_def
  by auto

lemma valid_labeled_state_final_labeled_state [simp]:
  shows "valid_labeled_state n (final_labeled_state n)"
proof-
  have "(replicate (Suc n) {})[n := {0..<n}] = (replicate n {}) @ [{0..<n}]"
    by (metis length_replicate list_update_length replicate_Suc replicate_append_same)
  then show ?thesis
    unfolding valid_labeled_state_def final_labeled_state_def
    by (auto simp del: replicate_Suc simp add: nth_append)
qed

lemma valid_labeled_move_valid_labeled_state:
  assumes "valid_labeled_state n l_state" "valid_labeled_move n l_state l_state'"
  shows "valid_labeled_state n l_state'"
proof-
  from assms obtain p1 p2 stone where 
    **: "p1 < p2" "p2 \<le> p1 + card (l_state ! p1)" "p2 \<le> n" "length l_state = n+1" "\<Union> (set l_state) = {0..<n}" "\<forall>i j. i < j \<and> j \<le> n \<longrightarrow> l_state ! i \<inter> l_state ! j = {}"
     "stone \<in> l_state ! p1" "l_state' = l_state[p1 := l_state ! p1 - {stone}, p2 := l_state ! p2 \<union> {stone}]"
    unfolding valid_labeled_move_def valid_labeled_move'_def valid_labeled_state_def Let_def labeled_move_def
    by auto

  then have *: "\<forall> i \<le> n. l_state' ! i = (if i = p1 then l_state ! p1 - {stone} 
                                         else if i = p2 then l_state ! p2 \<union> {stone}
                                         else l_state ! i)" "length l_state' = n + 1"
    by auto

  have "stone \<notin> l_state ! p2" 
    using \<open>\<forall>i j. i < j \<and> j \<le> n \<longrightarrow> l_state ! i \<inter> l_state ! j = {}\<close>  \<open>stone \<in> l_state ! p1\<close> 
    using \<open>p1 < p2\<close> \<open>p2 \<le> n\<close>
    by (metis Collect_mem_eq IntI empty_Collect_eq)

  have "\<forall> i \<le> n. i \<noteq> p1 \<longrightarrow> stone \<notin> l_state ! i"
    using \<open>\<forall>i j. i < j \<and> j \<le> n \<longrightarrow> l_state ! i \<inter> l_state ! j = {}\<close>  \<open>stone \<in> l_state ! p1\<close> 
    using \<open>p1 < p2\<close> \<open>p2 \<le> n\<close>
    by (metis disjoint_iff_not_equal le_less_trans less_imp_le_nat nat_neq_iff)

  have "\<Union> (set l_state') = \<Union> (set l_state)"
  proof safe
    fix x X
    assume "x \<in> X" "X \<in> set l_state'"
    then obtain i where "x \<in> l_state' ! i" "i \<le> n" 
      using \<open>length l_state' = n+1\<close>
      by (metis One_nat_def add.right_neutral add_Suc_right in_set_conv_nth le_simps(2))
      
    then show "x \<in> \<Union> (set l_state)"
      using * \<open>stone \<in> l_state ! p1\<close> **
      by (smt Diff_iff One_nat_def Un_insert_right add.right_neutral add_Suc_right boolean_algebra_cancel.sup0 insertE le_imp_less_Suc le_less_trans less_imp_le_nat mem_simps(9) nth_mem)
  next
    fix x X
    assume "x \<in> X" "X \<in> set l_state"
    then obtain i where "i \<le> n" "x \<in> l_state ! i"
      using \<open>length l_state = n + 1\<close>
      by (metis add.commute in_set_conv_nth le_simps(2) plus_1_eq_Suc)
    show "x \<in> \<Union> (set l_state')"
    proof (cases "i = p1")
      case True              
      then have "x \<in> l_state' ! p1 \<or> x \<in> l_state' ! p2"
        using * \<open>p1 < p2\<close> \<open>p2 \<le> n\<close> \<open>x \<in> l_state ! i\<close>
        by auto
      then show ?thesis
        using \<open>p1 < p2\<close> \<open>p2 \<le> n\<close>
        using "*"(2) mem_simps(9) nth_mem
        by auto
    next
      case False
      then have "x \<in> l_state' ! i"
        using * \<open>p1 < p2\<close> \<open>p2 \<le> n\<close> \<open>x \<in> l_state ! i\<close>
        using \<open>i \<le> n\<close> by auto
      then show ?thesis
        by (metis "*"(2) One_nat_def Sup_upper \<open>i \<le> n\<close> add.right_neutral add_Suc_right le_imp_less_Suc nth_mem subsetD)
    qed
  qed

  moreover

  have "\<forall>i j. i < j \<and> j \<le> n \<longrightarrow> l_state' ! i \<inter> l_state' ! j = {}"
  proof safe
    fix i j x
    assume ***: "i < j" "j \<le> n" "x \<in> l_state' ! i" "x \<in> l_state' ! j"
    then have False
      using * \<open>\<forall>i j. i < j \<and> j \<le> n \<longrightarrow> l_state ! i \<inter> l_state ! j = {}\<close>
      using \<open>stone \<in> l_state ! p1\<close> \<open>stone \<notin> l_state ! p2\<close> \<open>\<forall> i \<le> n. i \<noteq> p1 \<longrightarrow> stone \<notin> l_state ! i\<close>
      using \<open>length l_state = n+1\<close> \<open>length l_state' = n+1\<close> \<open>p1 < p2\<close> \<open>p2 \<le> n\<close> 
      apply (cases "j = p2")
      apply (smt Diff_insert_absorb Diff_subset IntI Un_insert_right boolean_algebra_cancel.sup0 empty_iff insertE less_imp_le_nat less_le_trans mk_disjoint_insert nat_neq_iff subsetD)
      apply (smt Un_insert_right boolean_algebra_cancel.sup0 disjoint_iff_not_equal insert_Diff insert_iff less_imp_le_nat less_le_trans)
      done
    then show "x \<in> {}"
      by simp
  qed

  ultimately

  show ?thesis
    unfolding valid_labeled_state_def
    using assms
    unfolding valid_labeled_move_def Let_def valid_labeled_move'_def labeled_move_def valid_labeled_state_def
    by auto
qed

lemma valid_labeled_moves_valid_labeled_states:
  assumes "valid_labeled_moves n l_states" "valid_labeled_state n (hd l_states)"
  shows "\<forall> state \<in> set l_states. valid_labeled_state n state"
  using assms
proof (induction l_states)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a states)
  then show ?case
    by (metis (no_types, lifting) Groups.add_ac(2) hd_Cons_tl length_greater_0_conv length_tl less_diff_conv list.inject list.set_cases list.simps(3) nth_Cons_0 nth_Cons_Suc plus_1_eq_Suc valid_labeled_moves_def valid_labeled_move_valid_labeled_state)
qed

lemma valid_labeled_game_valid_labeled_states:
  assumes "valid_labeled_game n states"
  shows "\<forall> state \<in> set states. valid_labeled_state n state"
  using assms
  unfolding valid_labeled_game_def
  using valid_labeled_moves_valid_labeled_states
  by fastforce

definition labeled_move_positions where
  "labeled_move_positions state state' = 
       (THE (p1, p2, stone). valid_labeled_move' (length state - 1) p1 p2 stone state state')"

lemma labeled_move_positions_unique:
  assumes "valid_labeled_state n state" "valid_labeled_move n state state'"
  shows "\<exists>! (p1, p2, stone). valid_labeled_move' n p1 p2 stone state state'"
proof-
  obtain p1 p2 stone where *: "valid_labeled_move' n p1 p2 stone state state'"
    using assms
    unfolding valid_labeled_move_def
    by auto
  show ?thesis
  proof
    show "case (p1, p2, stone) of (p1, p2, stone) \<Rightarrow> valid_labeled_move' n p1 p2 stone state state'"
      using *
      by auto
  next
    fix x :: "nat \<times> nat \<times> nat"
    obtain p1' p2' stone' where x: "x = (p1', p2', stone')"
      by (cases x)
    assume "case x of (p1, p2, stone) \<Rightarrow> valid_labeled_move' n p1 p2 stone state state'"
    then have **: "valid_labeled_move' n p1' p2' stone' state state'"
      using x
      by simp
    have *: "p1 < p2" "p2 \<le> n" "stone < n" "stone \<in> state ! p1" "stone \<notin> state' ! p1"  "stone \<notin> state ! p2" "stone \<in> state' ! p2" 
         "\<forall> stone'' p. p \<le> n \<and> stone'' < n \<and> stone'' \<noteq> stone \<longrightarrow> (stone'' \<in> state ! p \<longleftrightarrow> stone'' \<in> state' ! p)"
      using * assms(1)
      unfolding valid_labeled_state_def valid_labeled_move'_def Let_def labeled_move_def
      by (auto simp add: nth_list_update)

    have **: "p1' < p2'" "p2' \<le> n" "stone' < n" "stone' \<in> state ! p1'" "stone' \<notin> state' ! p1'"  "stone' \<notin> state ! p2'" "stone' \<in> state' ! p2'" 
         "\<forall> stone'' p. p \<le> n \<and> stone'' < n \<and> stone'' \<noteq> stone' \<longrightarrow> (stone'' \<in> state ! p \<longleftrightarrow> stone'' \<in> state' ! p)"
      using ** assms(1)
      unfolding valid_labeled_state_def valid_labeled_move'_def Let_def labeled_move_def
      by (auto simp add: nth_list_update)

    have "stone = stone'"
      using * **
      by auto

    have disj: "\<forall>i j. i < j \<and> j \<le> n \<longrightarrow> state ! i \<inter> state ! j = {}"
      using assms(1)
      unfolding valid_labeled_state_def
      by auto

    have "p1 = p1'"
      using *(4) **(4) \<open>stone = stone'\<close> *(1-2) **(1-2)
      using disj[rule_format, of p1 p1']
      using disj[rule_format, of p1' p1]
      by force

    have "valid_labeled_state n state'"
      using assms(1) assms(2) valid_labeled_move_valid_labeled_state by blast
    then have disj': "\<forall>i j. i < j \<and> j \<le> n \<longrightarrow> state' ! i \<inter> state' ! j = {}"
      unfolding valid_labeled_state_def
      by auto

    have "p2 = p2'"
      using *(7) **(7) \<open>stone = stone'\<close> *(2) **(2)
      using disj'[rule_format, of p2 p2']
      using disj'[rule_format, of p2' p2]
      by force

    then show "x = (p1, p2, stone)"
      using x \<open>stone = stone'\<close> \<open>p1 = p1'\<close> \<open>p2 = p2'\<close>
      by auto
  qed
qed

lemma labeled_move_positions:
  assumes "valid_labeled_state n state" "valid_labeled_move' n p1 p2 stone state state'"
  shows "labeled_move_positions state state' = (p1, p2, stone)"
  using assms
  using labeled_move_positions_unique[OF assms(1), of state']
  unfolding labeled_move_positions_def valid_labeled_state_def valid_labeled_move_def
  by auto (smt case_prodI the_equality)

lemma labeled_move_positions_valid_move':
  assumes "valid_labeled_state n state" "valid_labeled_move n state state'"
          "labeled_move_positions state state' = (p1, p2, stone)"
  shows "valid_labeled_move' n p1 p2 stone state state'"
  using assms(1) assms(2) assms(3) labeled_move_positions valid_labeled_move_def
  by auto

definition stone_position :: "labeled_state \<Rightarrow> nat \<Rightarrow> nat" where
  "stone_position l_state stone = 
     (THE k. k < length l_state \<and> stone \<in> l_state ! k)"

lemma stone_position_unique:
  assumes "valid_labeled_state n l_state" "stone < n"
  shows "\<exists>! k. k < length l_state \<and> stone \<in> l_state ! k"
proof-
  from assms have "stone \<in> \<Union> (set l_state)"
    unfolding valid_labeled_state_def
    by auto 
  then obtain k where *: "k < length l_state" "stone \<in> l_state ! k"
    by (metis UnionE in_set_conv_nth)
  then have "\<forall> k'. k' < length l_state \<and> stone \<in> l_state ! k' \<longrightarrow> k = k'"
    using assms
    unfolding valid_labeled_state_def
    by (metis IntI Suc_eq_plus1 empty_iff le_simps(2) nat_neq_iff)
  then show ?thesis
    using *
    by auto
qed

lemma stone_position:
  assumes "valid_labeled_state n l_state" "stone < n"
  shows "stone_position l_state stone \<le> n \<and> 
         stone \<in> l_state ! (stone_position l_state stone)"
  using assms stone_position_unique[OF assms]
  using theI[of "\<lambda> k. k < length l_state \<and> stone \<in> l_state ! k"]
  unfolding valid_labeled_state_def stone_position_def
  by (metis (mono_tags, lifting) One_nat_def add.right_neutral add_Suc_right le_simps(2))

lemma stone_positionI:
  assumes "valid_labeled_state n l_state" "stone < n" 
          "k < length l_state" "stone \<in> l_state ! k"
  shows "stone_position l_state stone = k"
  unfolding stone_position_def
  using assms stone_position_unique
  by blast

lemma valid_labeled_move'_stone_positions:
  assumes "valid_labeled_state n l_state" "valid_labeled_move' n p1 p2 stone l_state l_state'"
  shows "stone_position l_state stone = p1 \<and> stone_position l_state' stone = p2"
proof safe
  show "stone_position l_state stone = p1"
  proof (rule stone_positionI)
    show "valid_labeled_state n l_state" "stone < n" "p1 < length l_state" "stone \<in> l_state ! p1"
      using assms
      unfolding valid_labeled_state_def valid_labeled_move'_def Let_def
      by auto
  qed
next
  show "stone_position l_state' stone = p2"
  proof (rule stone_positionI)
    show "valid_labeled_state n l_state'"
      using assms(1) assms(2) valid_labeled_move_def valid_labeled_move_valid_labeled_state
      by blast
  next
    show "stone < n" "p2 < length l_state'" "stone \<in> l_state' ! p2"
      using assms
      unfolding valid_labeled_state_def valid_labeled_move'_def Let_def labeled_move_def
      by auto
  qed
qed

lemma valid_labeled_move'_stone_positions_other:
  assumes "valid_labeled_state n l_state" "valid_labeled_move' n p1 p2 stone l_state l_state'"
  shows "\<forall> stone'. stone' \<noteq> stone \<and> stone' < n \<longrightarrow> 
                     stone_position l_state' stone' = stone_position l_state stone'"
proof safe
  fix stone'
  assume "stone' < n" "stone' \<noteq> stone"
  show "stone_position l_state' stone' = stone_position l_state stone'"
  proof (rule stone_positionI)
    show "stone' < n"
      by fact
  next
    show "valid_labeled_state n l_state'"
      using assms
      using valid_labeled_move_def valid_labeled_move_valid_labeled_state
      by blast
  next
    show "stone_position l_state stone' < length l_state'"
      using \<open>stone' < n\<close> assms(1-2) stone_position[of n l_state stone']
      unfolding valid_labeled_state_def
      by (metis Suc_eq_plus1 labeled_move_def le_imp_less_Suc length_list_update valid_labeled_move'_def)
  next
    show "stone' \<in> l_state' ! stone_position l_state stone'"
    proof-
      have "stone' \<in> l_state ! stone_position l_state stone'" 
           "stone_position l_state stone' < length l_state"
        using \<open>stone' < n\<close> assms(1-2) stone_position[of n l_state stone']
        unfolding valid_labeled_state_def
        by auto
      then show ?thesis
        using \<open>stone' \<noteq> stone\<close> \<open>valid_labeled_move' n p1 p2 stone l_state l_state'\<close>
        unfolding valid_labeled_move'_def labeled_move_def Let_def
        by (metis (no_types, lifting) Un_insert_right boolean_algebra_cancel.sup0 insert_Diff insert_iff length_list_update nth_list_update_eq nth_list_update_neq)
    qed
  qed
qed

subsubsection \<open>Unlabel\<close>

definition unlabel :: "labeled_state \<Rightarrow> state" where 
  "unlabel = map card"

lemma unlabel_initial [simp]:
  shows "unlabel (initial_labeled_state n) = initial_state n"
  unfolding initial_labeled_state_def initial_state_def unlabel_def
  by auto

lemma unlabel_final [simp]:
  shows "unlabel (final_labeled_state n) = final_state n"
  unfolding final_labeled_state_def final_state_def unlabel_def
  by (metis card_atLeastLessThan card_empty diff_zero map_replicate map_update)

lemma unlabel_valid:
  assumes "valid_labeled_state n l_state"
  shows "valid_state n (unlabel l_state)"
  unfolding valid_state_def unlabel_def
proof
  let ?state = "map card l_state"
  show "length ?state = n + 1"
    using assms
    by (simp add: valid_labeled_state_def)

  show "sum_list ?state = n"
  proof-
    let ?s = "filter (\<lambda> y. card y \<noteq> 0) l_state"

    have "(\<Sum> x \<leftarrow> l_state. card x) = (\<Sum> x \<leftarrow> ?s. card x)"
      by (metis (mono_tags, lifting) sum_list_map_filter)
    also have "... = (\<Sum> x \<in> set ?s. card x)"
    proof-
      have "\<forall>i j. i < j \<and> j < length l_state \<longrightarrow> l_state ! i \<inter> l_state ! j = {}"
        using assms
        unfolding valid_labeled_state_def
        by simp
      then have "distinct ?s"
      proof (induction l_state)
        case Nil
        then show ?case
          by simp
      next
        case (Cons a l_state)
        have "\<forall>i j. i < j \<and> j < length l_state \<longrightarrow> l_state ! i \<inter> l_state ! j = {}"
          using Cons(2)
          by (metis One_nat_def Suc_eq_plus1 Suc_less_eq list.size(4) nth_Cons_Suc)
        then have "distinct (filter (\<lambda>y. card y \<noteq> 0) l_state)"
          using Cons(1)
          by simp
        moreover
        have "card a > 0 \<longrightarrow> a \<notin> set l_state"
        proof safe
          assume "card a > 0" "a \<in> set l_state"
          show False
            using Cons(2)[rule_format, of 0] \<open>0 < card a\<close> \<open>a \<in> set l_state\<close> 
            by (metis card_empty in_set_conv_nth inf.idem le_simps(2) length_Cons not_le nth_Cons_0 nth_Cons_Suc zero_less_Suc)
        qed
        ultimately
        show ?case
          using Cons
          by auto
      qed
      then show ?thesis
        using sum_list_distinct_conv_sum_set by blast
    qed
    also have "... = card (\<Union> (set ?s))"
    proof-
      have "\<forall>i\<in>set ?s. finite (id i)"
        using assms
        unfolding valid_labeled_state_def
        by fastforce
      moreover
      have "\<forall>i\<in>set ?s.
            \<forall>j\<in>set ?s. i \<noteq> j \<longrightarrow> id i \<inter> id j = {}"
      proof (rule ballI, rule ballI, rule impI)
        fix i j
        assume "i \<in> set ?s" "j \<in> set ?s" "i \<noteq> j"
        then obtain i' j' where "i = l_state ! i'" "j = l_state ! j'" "i' \<le> n" "j' \<le> n"
          using assms
          unfolding valid_labeled_state_def
          by (metis Suc_eq_plus1 filter_is_subset in_set_conv_nth le_simps(2) subsetD)
        then show "id i \<inter> id j = {}"
          using assms \<open>i \<noteq> j\<close>
          unfolding valid_labeled_state_def
          by (metis disjoint_iff_not_equal id_apply nat_neq_iff)
      qed
      ultimately
      show ?thesis
        using card_UN_disjoint[of "set ?s" id, symmetric]
        by simp
    qed
    also have "card (\<Union> (set ?s)) = card (\<Union> (set l_state))"
    proof-
      have "\<Union> (set ?s) = \<Union> (set l_state)"
      proof
        show "\<Union> (set l_state) \<subseteq> \<Union> (set ?s)"
        proof safe
          fix x X
          assume *: "x \<in> X" "X \<in> set l_state"
          then have "card X \<noteq> 0"
            using assms
            unfolding valid_labeled_state_def
            using Union_upper finite_subset
            by fastforce
          then show "x \<in> \<Union> (set ?s)"
            using *
            by auto
        qed
      qed auto
      then show ?thesis
        by simp
    qed
    finally
    show ?thesis
      using assms
      unfolding valid_labeled_state_def
      by simp
  qed
qed

lemma unlabel_valid_move':
  assumes "valid_labeled_state n l_state" "valid_labeled_move' n p1 p2 stone l_state l_state'"
  shows "valid_move' n p1 p2 (unlabel l_state) (unlabel l_state') \<and> 
         unlabel l_state' = move p1 p2 (unlabel l_state)"
proof-
  from assms have
    "p1 < p2" "p2 \<le> p1 + card (l_state ! p1)" "p2 \<le> n" "length l_state = n+1" "\<Union> (set l_state) = {0..<n}" "\<forall>i j. i < j \<and> j \<le> n \<longrightarrow> l_state ! i \<inter> l_state ! j = {}"
     "stone \<in> l_state ! p1" "l_state' = l_state[p1 := l_state ! p1 - {stone}, p2 := l_state ! p2 \<union> {stone}]"
    unfolding valid_labeled_move_def valid_labeled_move'_def valid_labeled_state_def unlabel_def Let_def labeled_move_def
    by auto
  
  have "finite (l_state ! p1) \<and> finite (l_state ! p2)"
    using \<open>\<Union> (set l_state) = {0..<n}\<close>
    using \<open>length l_state = n + 1\<close> \<open>p1 < p2\<close> \<open>p2 \<le> n\<close>
    by (metis One_nat_def Union_upper add.right_neutral add_Suc_right finite_atLeastLessThan finite_subset le_imp_less_Suc le_less_trans less_imp_le_nat nth_mem)

  have "stone \<notin> l_state ! p2"
    using \<open>stone \<in> l_state ! p1\<close> \<open>\<forall>i j. i < j \<and> j \<le> n \<longrightarrow> l_state ! i \<inter> l_state ! j = {}\<close>
    using \<open>length l_state = n + 1\<close> \<open>p1 < p2\<close> \<open>p2 \<le> n\<close>
    by (metis Collect_empty_eq Collect_mem_eq IntI)

  have "card (l_state ! p1) > 0" "length l_state' = length l_state"
       "card (l_state' ! p1) = card (l_state ! p1) - 1"  "card (l_state' ! p2) = card (l_state ! p2) + 1"
       "\<forall> p. p \<le> n \<and> p \<noteq> p1 \<and> p \<noteq> p2 \<longrightarrow> card (l_state' ! p) = card (l_state ! p)"
    using \<open>finite (l_state ! p1) \<and> finite (l_state ! p2)\<close> \<open>stone \<in> l_state ! p1\<close> 
    using \<open>stone \<notin> l_state ! p2\<close> \<open>l_state' = l_state[p1 := l_state ! p1 - {stone}, p2 := l_state ! p2 \<union> {stone}]\<close>
    using \<open>length l_state = n + 1\<close> \<open>p1 < p2\<close> \<open>p2 \<le> n\<close>
    using card_0_eq
    by - (blast, simp+)

  then show ?thesis
    using \<open>length l_state = n + 1\<close> \<open>p1 < p2\<close> \<open>p2 \<le> p1 + card (l_state ! p1)\<close> \<open>p2 \<le> n\<close>
    using \<open>l_state' = l_state[p1 := l_state ! p1 - {stone}, p2 := l_state ! p2 \<union> {stone}]\<close>
    unfolding unlabel_def valid_move'_def
    by (auto simp add: move_def map_update)
qed

lemma unlabel_valid_move:
  assumes "valid_labeled_state n l_state" "valid_labeled_move n l_state l_state'"
  shows "valid_move n (unlabel l_state) (unlabel l_state')"
  using assms(2) unlabel_valid_move'[OF assms(1)]
  unfolding valid_labeled_move_def valid_move_def Let_def
  by force


subsubsection \<open>Labeled move max stone\<close>

definition valid_labeled_move_max_stone :: "nat \<Rightarrow> labeled_state \<Rightarrow> labeled_state \<Rightarrow> bool" where 
  "valid_labeled_move_max_stone n l_state l_state' \<longleftrightarrow> 
      (\<exists> p1 p2. valid_labeled_move' n p1 p2 (Max (l_state ! p1)) l_state l_state')"

definition valid_labeled_moves_max_stone where
  "valid_labeled_moves_max_stone n l_states \<longleftrightarrow> 
     (\<forall> i < length l_states - 1. valid_labeled_move_max_stone n (l_states ! i) (l_states ! (i + 1)))"

definition valid_labeled_game_max_stone where
  "valid_labeled_game_max_stone n l_states \<longleftrightarrow> 
       length l_states \<ge> 2 \<and>
       hd l_states = initial_labeled_state n \<and> 
       last l_states = final_labeled_state n \<and> 
       valid_labeled_moves_max_stone n l_states"

lemma valid_labeled_moves_max_stone_Cons:
  assumes "valid_labeled_moves_max_stone n states" "valid_labeled_move_max_stone n state (hd states)"
  shows "valid_labeled_moves_max_stone n (state # states)"
  using assms
  using less_Suc_eq_0_disj
  apply (cases states)
  apply (simp add: valid_labeled_moves_max_stone_def)
  apply (auto simp add: valid_labeled_moves_max_stone_def)
  done

lemma valid_labeled_game_max_stone_valid_labeled_game:
  assumes "valid_labeled_game_max_stone n states"
  shows "valid_labeled_game n states"
  using assms
  unfolding valid_labeled_game_max_stone_def
  unfolding valid_labeled_game_def valid_labeled_moves_def valid_labeled_moves_max_stone_def
  unfolding valid_labeled_move_max_stone_def valid_labeled_move_def
  by force

lemma valid_labeled_move_move_max_stone:
  assumes "valid_labeled_state n l_state"
          "unlabel l_state = state" "valid_move' n p1 p2 state state'"
          "l_state' = labeled_move p1 p2 (Max (l_state ! p1)) l_state"
        shows "valid_labeled_move' n p1 p2 (Max (l_state ! p1)) l_state l_state'"
proof-
  have "Max (l_state ! p1) \<in> l_state ! p1"
    by (metis (no_types, lifting) Max_in assms(1) assms(2) assms(3) card_empty card_infinite less_le_trans nat_neq_iff nth_map trans_less_add1 unlabel_def valid_labeled_state_def valid_move'_def)
  then show ?thesis
    using assms
    by (metis (no_types, lifting) less_le_trans nth_map trans_less_add1 unlabel_def valid_labeled_move'_def valid_labeled_state_def valid_move'_def)
qed  

primrec label_moves_max_stone where
  "label_moves_max_stone l_state [] = [l_state]"
| "label_moves_max_stone l_state (state' # states) = 
     (let state = unlabel l_state;
          (p1, p2) = move_positions state state';
          l_state' = labeled_move p1 p2 (Max (l_state ! p1)) l_state
       in l_state # label_moves_max_stone l_state' states)"

lemma hd_label_moves_max_stone [simp]:
  shows "hd (label_moves_max_stone l_state states) = l_state"
  by (induction states) (auto simp add: Let_def split: prod.split)

lemma valid_states_label_moves_max_stone:
  assumes "valid_labeled_state n l_state" "valid_moves n (unlabel l_state # states)"
  shows "\<forall> l_state' \<in> set (label_moves_max_stone l_state states). valid_labeled_state n l_state'"
  using assms
proof (induction states arbitrary: l_state)
  case Nil
  then show ?case
    by simp
next
  case (Cons state' states)
  let ?state = "unlabel l_state"
  let ?p = "move_positions ?state state'"
  let ?p1 = "fst ?p"
  let ?p2 = "snd ?p"
  let ?stone = "Max (l_state ! ?p1)"
  let ?l_state' = "labeled_move ?p1 ?p2 ?stone l_state"

  have "valid_state n ?state"
    using \<open>valid_labeled_state n l_state\<close>
    by (simp add: unlabel_valid)

  have "valid_move n ?state state'"
    using Cons(3)
    by (metis Groups.add_ac(2) One_nat_def add_diff_cancel_left' add_is_0 gr0I list.size(4) n_not_Suc_n nth_Cons_0 nth_Cons_Suc plus_1_eq_Suc valid_moves_def)

  have "valid_move' n ?p1 ?p2 ?state state'"
    using \<open>valid_state n ?state\<close> \<open>valid_move n ?state state'\<close>
    by (simp add: move_positions_valid_move')

  have **: "valid_labeled_move' n ?p1 ?p2 ?stone l_state ?l_state'"
  proof (rule valid_labeled_move_move_max_stone)
    show "valid_labeled_state n l_state"
      by fact
  next
    show "unlabel l_state = unlabel l_state"
      by simp
  next
    show "valid_move' n ?p1 ?p2 ?state state'"
      by fact
  qed simp

  have "move ?p1 ?p2 ?state = state'"
    using \<open>valid_move' n ?p1 ?p2 ?state state'\<close>
    unfolding valid_move'_def Let_def
    by simp
  then have *: "unlabel ?l_state' = state'"
    using unlabel_valid_move'[OF Cons(2) **, THEN conjunct2]
    by simp
    
  have "\<forall> l_state' \<in> set (label_moves_max_stone ?l_state' states). valid_labeled_state n l_state'"
  proof (rule Cons(1))
    have "valid_labeled_move n l_state ?l_state'"
      using **
      unfolding valid_labeled_move_def
      by metis
    then show "valid_labeled_state n ?l_state'"
      using Cons(2)
      using valid_labeled_move_valid_labeled_state
      by blast
  next
    show "valid_moves n (unlabel ?l_state' # states)"
      using Cons(3) \<open>valid_move n (unlabel l_state) state'\<close>
      using *
      by (metis (no_types, lifting) One_nat_def add_Suc_right diff_add_inverse2 group_cancel.add1 less_diff_conv list.size(4) nth_Cons_Suc plus_1_eq_Suc valid_moves_def)
  qed
  then show ?case
    using Cons(2)
    by (metis (mono_tags, lifting) label_moves_max_stone.simps(2) prod.collapse prod.simps(2) set_ConsD)
qed

lemma unlabel_label_moves_max_stone:
  assumes "valid_labeled_state n l_state"  "valid_moves n (unlabel l_state # states)"
  shows "map unlabel (label_moves_max_stone l_state states) = unlabel l_state # states"
  using assms
proof (induction states arbitrary: l_state)
  case Nil
  then show ?case
    by simp
next
  case (Cons state' states)
  let ?state = "unlabel l_state"
  let ?p = "move_positions ?state state'"
  let ?p1 = "fst ?p"
  let ?p2 = "snd ?p"
  let ?stone = "Max (l_state ! ?p1)"
  let ?l_state' = "labeled_move ?p1 ?p2 ?stone l_state"

  have "valid_state n ?state"
    using \<open>valid_labeled_state n l_state\<close>
    by (simp add: unlabel_valid)

  have "valid_move n ?state state'"
    using Cons(3)
    by (metis Groups.add_ac(2) One_nat_def add_diff_cancel_left' add_is_0 gr0I list.size(4) n_not_Suc_n nth_Cons_0 nth_Cons_Suc plus_1_eq_Suc valid_moves_def)

  have "valid_move' n ?p1 ?p2 ?state state'"
    using \<open>valid_state n ?state\<close> \<open>valid_move n ?state state'\<close>
    by (simp add: move_positions_valid_move')

  have **: "valid_labeled_move' n ?p1 ?p2 ?stone l_state ?l_state'"
  proof (rule valid_labeled_move_move_max_stone)
    show "valid_labeled_state n l_state"
      by fact
  next
    show "unlabel l_state = unlabel l_state"
      by simp
  next
    show "valid_move' n ?p1 ?p2 ?state state'"
      by fact
  qed simp

  have "move ?p1 ?p2 ?state = state'"
    using \<open>valid_move' n ?p1 ?p2 ?state state'\<close>
    unfolding valid_move'_def Let_def
    by simp
  then have *: "unlabel ?l_state' = state'"
    using unlabel_valid_move'[OF Cons(2) **, THEN conjunct2]
    by simp

  have "map unlabel (label_moves_max_stone ?l_state' states) = unlabel ?l_state' # states"
  proof (rule Cons(1))
    show "valid_moves n ((unlabel ?l_state') # states)"
      using Cons(3) *
      using less_diff_conv valid_moves_def
      by auto
  next
    have "valid_labeled_move n l_state ?l_state'"
      using **
      unfolding valid_labeled_move_def
      by metis
    then show "valid_labeled_state n ?l_state'"
      using Cons(2)
      using valid_labeled_move_valid_labeled_state
      by blast
  qed                                                 
  then show ?case
    using * \<open>valid_move' n ?p1 ?p2 (unlabel l_state) state'\<close> \<open>valid_state n (unlabel l_state)\<close> 
    by (smt Cons_eq_map_conv case_prod_conv label_moves_max_stone.simps(2) valid_move'_move_positions)
qed

lemma label_moves_max_stone_length [simp]:
  shows "length (label_moves_max_stone l_state states) = length states + 1"
  by (induction states arbitrary: l_state) (auto split: prod.split)

lemma label_moves_max_stone_valid_moves:
  assumes "valid_labeled_state n l_state" "valid_moves n (unlabel l_state # states)"
  shows "valid_labeled_moves_max_stone n (label_moves_max_stone l_state states)"
  using assms
proof (induction states arbitrary: l_state)
  case Nil
  then show ?case
    by (simp add: valid_labeled_moves_max_stone_def)
next
  case (Cons state' states)
  let ?state = "unlabel l_state"
  let ?p = "move_positions ?state state'"
  let ?p1 = "fst ?p"
  let ?p2 = "snd ?p"
  let ?stone = "Max (l_state ! ?p1)"
  let ?l_state' = "labeled_move ?p1 ?p2 ?stone l_state"

  have "valid_state n ?state"
    using \<open>valid_labeled_state n l_state\<close>
    by (simp add: unlabel_valid)

  have "valid_move n ?state state'"
    using Cons(3)
    by (metis Groups.add_ac(2) One_nat_def add_diff_cancel_left' add_is_0 gr0I list.size(4) n_not_Suc_n nth_Cons_0 nth_Cons_Suc plus_1_eq_Suc valid_moves_def)

  have "valid_move' n ?p1 ?p2 ?state state'"
    using \<open>valid_state n ?state\<close> \<open>valid_move n ?state state'\<close>
    by (simp add: move_positions_valid_move')

  have **: "valid_labeled_move' n ?p1 ?p2 ?stone l_state ?l_state'"
  proof (rule valid_labeled_move_move_max_stone)
    show "valid_labeled_state n l_state"
      by fact
  next
    show "unlabel l_state = unlabel l_state"
      by simp
  next
    show "valid_move' n ?p1 ?p2 ?state state'"
      by fact
  qed simp

  have "move ?p1 ?p2 ?state = state'"
    using \<open>valid_move' n ?p1 ?p2 ?state state'\<close>
    unfolding valid_move'_def Let_def
    by simp
  then have *: "unlabel ?l_state' = state'"
    using unlabel_valid_move'[OF Cons(2) **, THEN conjunct2]
    by simp

  have ***: "valid_labeled_move_max_stone n l_state ?l_state'"
    using **
    unfolding valid_labeled_move_max_stone_def
    by blast

  have "valid_labeled_moves_max_stone n (label_moves_max_stone ?l_state' states)"
  proof (rule Cons(1))
    show "valid_moves n ((unlabel ?l_state') # states)"
      using Cons(3) *
      using less_diff_conv valid_moves_def
      by auto
    have "valid_labeled_move n l_state ?l_state'"
      using **
      unfolding valid_labeled_move_def
      by metis
    then show "valid_labeled_state n ?l_state'"
      using Cons(2)
      using valid_labeled_move_valid_labeled_state
      by blast
  qed
  moreover
  have "hd (label_moves_max_stone ?l_state' states) = ?l_state'"
    using hd_label_moves_max_stone by blast
  ultimately
  show ?case
    using *** \<open>valid_move' n ?p1 ?p2 ?state state'\<close> \<open>valid_state n ?state\<close> 
    using valid_labeled_moves_max_stone_Cons
    by (metis (mono_tags, lifting) case_prod_conv label_moves_max_stone.simps(2) valid_move'_move_positions)
qed

lemma final_labeled_state_unique:
  assumes "unlabel l_state = final_state n" "valid_labeled_state n l_state"
  shows "l_state = final_labeled_state n"
proof-
  have "\<forall> i \<le> n. finite (l_state ! i)"
    by (metis Groups.add_ac(2) Union_upper assms(2) finite_atLeastLessThan finite_subset le_imp_less_Suc nth_mem plus_1_eq_Suc valid_labeled_state_def)
  moreover
  have "\<forall> i < n. card (l_state ! i) = 0"
    using assms
    unfolding unlabel_def final_state_def valid_labeled_state_def
    by (metis One_nat_def add.right_neutral add_Suc_right le_imp_less_Suc less_imp_le_nat nat_neq_iff nth_list_update_neq nth_map nth_replicate)
  moreover
  have "card (l_state ! n) = n"
    using assms
    unfolding unlabel_def final_state_def valid_labeled_state_def
    by (metis length_replicate less_add_same_cancel1 less_one nth_list_update_eq nth_map)
  moreover
  have "\<Union> (set l_state) = {0..<n}" "length l_state = n + 1"
    using assms
    unfolding unlabel_def final_state_def valid_labeled_state_def
    by simp_all
  ultimately
  have "\<forall> i < n. l_state ! i = {}" "l_state ! n = {0..<n}"
     apply -
     apply auto[1]
    apply (metis Union_upper assms(2) card_atLeastLessThan card_subset_eq diff_zero finite_atLeastLessThan less_add_same_cancel1 nth_mem valid_labeled_state_def zero_less_one)
    done
  show ?thesis
  proof (rule nth_equalityI)
    show "length l_state = length (final_labeled_state n)"
      using \<open>length l_state = n + 1\<close>
      unfolding final_labeled_state_def
      by (simp del: replicate_Suc)
  next
    fix i
    assume "i < length l_state"
    then show "l_state ! i = final_labeled_state n ! i"
      using \<open>\<forall> i < n. l_state ! i = {}\<close> \<open>l_state ! n = {0..<n}\<close> \<open>length l_state = n + 1\<close>
      unfolding final_labeled_state_def
      by (metis add.commute length_replicate less_Suc_eq nth_list_update_eq nth_list_update_neq nth_replicate plus_1_eq_Suc)
  qed
qed

lemma labeled_game_max_stone_length [simp]:
  assumes "valid_game n states"
  shows "length (label_moves_max_stone (initial_labeled_state n) (tl states)) = length states"
  by (metis assms hd_Cons_tl length_map list.size(3) not_le unlabel_initial unlabel_label_moves_max_stone valid_game_def valid_labeled_state_initial_labeled_state zero_less_numeral)
                                                     
lemma valid_labeled_game_max_stone:
  assumes "valid_game n states"
  shows "valid_labeled_game_max_stone n (label_moves_max_stone (initial_labeled_state n) (tl states))"
  unfolding valid_labeled_game_max_stone_def
proof safe
  let ?l_states = "label_moves_max_stone (initial_labeled_state n) (tl states)"
  have "valid_moves n (unlabel (initial_labeled_state n) # tl states)"
    using assms
    by (metis Groups.add_ac(2) One_nat_def add_diff_cancel_left' hd_Cons_tl list.sel(2) list.size(3) list.size(4) n_not_Suc_n plus_1_eq_Suc unlabel_initial upt_0 upt_rec valid_game_def valid_moves_def)
  then have *: "map unlabel ?l_states = (initial_state n) # tl states"
    using unlabel_label_moves_max_stone[of n "initial_labeled_state n" "tl states"]
    by simp

  have "unlabel (hd ?l_states) = initial_state n"
    using *
    by auto
  then show "hd ?l_states = initial_labeled_state n"
    by simp

  have "unlabel (last ?l_states) = final_state n"
    using assms
    unfolding valid_game_def
    by (metis "*" Nil_is_map_conv hd_Cons_tl last_map list.size(3) not_le zero_less_numeral)
  moreover
  have "valid_labeled_state n (last ?l_states)"
    using * \<open>valid_moves n (unlabel (initial_labeled_state n) # tl states)\<close>
    by (metis last_in_set list.discI list.simps(8) valid_labeled_state_initial_labeled_state valid_states_label_moves_max_stone)
  ultimately
  show "last ?l_states = final_labeled_state n"
    using final_labeled_state_unique
    by blast

  show "valid_labeled_moves_max_stone n (label_moves_max_stone (initial_labeled_state n) (tl states))"
  proof (rule label_moves_max_stone_valid_moves)
    show "valid_labeled_state n (initial_labeled_state n)"
      by simp
  next
    show "valid_moves n (unlabel (initial_labeled_state n) # tl states)"
      by fact
  qed
next
  show "2 \<le> length (label_moves_max_stone (initial_labeled_state n) (tl states))"
    using assms
    unfolding valid_game_def
    by auto
qed

subsubsection \<open>Valid labeled game move max stone length\<close>

lemma moved_from:
  assumes "valid_labeled_state n (hd l_states)" "valid_labeled_moves n l_states"
          "i < j" "j < length l_states" "stone < n"
          "stone_position (l_states ! i) stone \<noteq> stone_position (l_states ! j) stone"
  shows "(\<exists> k. i \<le> k \<and> k < j \<and> 
         (let (p1, p2, stone') = labeled_move_positions (l_states ! k) (l_states ! (k + 1)) in 
          stone' = stone \<and> p1 = stone_position (l_states ! i) stone))"
  using assms
proof (induction l_states arbitrary: i j)
  case Nil
  then show ?case
    by simp
next
  case (Cons l_state l_states)
  obtain p1 p2 stone' where 
    *: "(p1, p2, stone') = labeled_move_positions ((l_state # l_states) ! i) ((l_state # l_states) ! (i + 1))"
    by (metis prod_cases3)

  moreover

  have ***: "valid_labeled_state n ((l_state # l_states) ! i)"
    using Cons(2-5)
    by (meson less_imp_le_nat less_le_trans nth_mem valid_labeled_moves_valid_labeled_states)

  moreover

  have "valid_labeled_move n ((l_state # l_states) ! i) ((l_state # l_states) ! (i + 1))"
    using Cons(3-5)
    unfolding valid_labeled_moves_def
    by auto

  ultimately

  have **: "valid_labeled_move' n p1 p2 stone' ((l_state # l_states) ! i) ((l_state # l_states) ! (i + 1))"
    using labeled_move_positions_valid_move'
    by simp
    
  show ?case
  proof (cases "stone' = stone")
    case True
    have "p1 = stone_position ((l_state # l_states) ! i) stone'"
      using **
      using \<open>valid_labeled_state n ((l_state # l_states) ! i)\<close> valid_labeled_move'_stone_positions
      by blast
    then show ?thesis
      using * Cons(4) True
      by (rule_tac x=i in exI, auto)
  next
    case False
    
    have "stone_position ((l_state # l_states) ! (i + 1)) stone = stone_position ((l_state # l_states) ! i) stone"
      using valid_labeled_move'_stone_positions_other[OF *** **] \<open>stone' \<noteq> stone\<close> \<open>stone < n\<close>
      by auto
   then have *: "stone_position (l_states ! i) stone \<noteq> stone_position (l_states ! (j - 1)) stone"
      using Cons(4) Cons(7)
      by auto
    moreover
    have "valid_labeled_state n (hd l_states)"
    proof-
      have "l_states \<noteq> []"
        using Cons(4) Cons(5) *
        by auto
      then show ?thesis
        using Cons(2-3)
        by (meson hd_in_set list.set_intros(2) valid_labeled_moves_valid_labeled_states)
    qed

    moreover
    have "valid_labeled_moves n l_states"
      using Cons(3)
      using Groups.add_ac(2) less_diff_conv valid_labeled_moves_def
      by auto
    moreover
    have "i < j - 1" 
      using Cons(4) *
      using less_antisym plus_1_eq_Suc
      by fastforce
    moreover
    have "j - 1 < length l_states"
      using \<open>i < j\<close> Cons(5)
      by auto
    ultimately
    obtain k where "i \<le> k" "k < j - 1"
         "let (p1, p2, stone') = labeled_move_positions (l_states ! k) (l_states ! (k + 1)) in 
          stone' = stone \<and> p1 = stone_position (l_states ! i) stone"
      using Cons(1)[of "i" "j-1"] \<open>stone < n\<close>
      by (auto simp add: nth_Cons)
    then show ?thesis
      using \<open>stone_position ((l_state # l_states) ! (i + 1)) stone = stone_position ((l_state # l_states) ! i) stone\<close>
      by (rule_tac x="k+1" in exI) (auto simp add: Let_def nth_Cons)
  qed
qed

lemma valid_labeled_game_max_stone_min_length:
  assumes "valid_labeled_game_max_stone n l_states"
  shows "length l_states \<ge> (\<Sum> k \<leftarrow> [1..<n+1]. (ceiling (n / k))) + 1"
  using assms
proof-
  have "l_states \<noteq> []" "length l_states \<ge> 2" "valid_labeled_state n (hd l_states)" "valid_labeled_moves n l_states"
    using assms
    using valid_labeled_game_max_stone_def
    using valid_labeled_game_def valid_labeled_game_max_stone_valid_labeled_game 
    by auto

  let ?ss = "map (\<lambda> (state, state'). (state, labeled_move_positions state state')) (zip (butlast l_states) (tl l_states))"
  let ?sstone = "\<lambda> stone. filter (\<lambda> (state, p1, p2, stone'). stone' = stone) ?ss"

  have "(\<Sum> k \<leftarrow> [1..<n+1]. (ceiling (n / k))) = 
        (\<Sum> stone \<leftarrow> [0..<n]. (ceiling (n / (stone + 1))))"
  proof-
    have "map (\<lambda>x. x + 1) [0..<n] = [1..<n+1]"
      using map_add_upt by blast
    then show ?thesis
      by (subst sum_list_comp, simp)
  qed
  also have "... \<le> (\<Sum> stone \<leftarrow> [0..<n]. int (length (?sstone stone)))"
  proof (rule sum_list_mono)           
    fix stone
    assume "stone \<in> set [0..<n]"
    show "ceiling (n / (stone + 1)) \<le> int (length (?sstone stone))"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "ceiling (n / (stone + 1)) > int (length (?sstone stone))"
        by simp
      then have "int (length (?sstone stone)) * (stone + 1) < n"
        using lt_ceiling_frac
        by simp
      then have "length (?sstone stone) * (stone + 1) < n"
        by (metis (mono_tags, lifting) of_nat_less_imp_less of_nat_mult)

      obtain ss where ss: "ss = ?sstone stone"
        by auto

      have valid_moves': "\<forall> (state, p1, p2, stone') \<in> set ss. stone' =  Max (state ! p1) \<and> (\<exists> state'. valid_labeled_move' n p1 p2 stone' state state')"
      proof safe
        fix state p1 p2 stone' 
        assume "(state, p1, p2, stone') \<in> set ss"
        then have "(state, p1, p2, stone') \<in> set ?ss"
          using ss
          by auto
        then obtain state' where
          "(state, p1, p2, stone') = (state, labeled_move_positions state state')"
          "(state, state') \<in> set (zip (butlast l_states) (tl l_states))"
          by auto
        then obtain i where "i < length ((zip (butlast l_states) (tl l_states)))" "(zip (butlast l_states) (tl l_states)) ! i = (state, state')"
          by (meson in_set_conv_nth)
        then have "i < length l_states - 1" "l_states ! i = state" "l_states ! (i + 1) = state'"
          using nth_butlast[of i l_states] nth_tl[of i l_states]
          by simp_all
        then have "valid_labeled_move_max_stone n state state'"
          using \<open>valid_labeled_game_max_stone n l_states\<close>
          unfolding valid_labeled_game_max_stone_def valid_labeled_moves_max_stone_def
          by auto
        moreover 
        have "valid_labeled_state n state"
          using \<open>i < length l_states - 1\<close> \<open>l_states ! i = state\<close>
          by (meson add_lessD1 assms(1) less_diff_conv nth_mem valid_labeled_game_max_stone_valid_labeled_game valid_labeled_game_valid_labeled_states)          
        ultimately
        have *: "valid_labeled_move' n p1 p2 (Max (state ! p1)) state state'"
          using labeled_move_positions valid_labeled_move_max_stone_def
          using \<open>(state, p1, p2, stone') = (state, labeled_move_positions state state')\<close>
          by auto

        show "stone' = Max (state ! p1)"
          using \<open>(state, p1, p2, stone') = (state, labeled_move_positions state state')\<close> \<open>valid_labeled_move' n p1 p2 (Max (state ! p1)) state state'\<close> \<open>valid_labeled_state n state\<close> labeled_move_positions by auto

        then show "(\<exists> state'. valid_labeled_move' n p1 p2 stone' state state')"
          using *
          by blast
      qed

      have pos0: "stone_position (l_states ! 0) stone = 0"
        using \<open>stone \<in> set [0..<n]\<close> \<open>l_states \<noteq> []\<close>
        using \<open>valid_labeled_game_max_stone n l_states\<close>
        using stone_positionI[of n "l_states ! 0" stone 0]
        using hd_conv_nth[of l_states, symmetric]
        using valid_labeled_state_initial_labeled_state
        unfolding valid_labeled_game_max_stone_def initial_labeled_state_def
        by auto

      have posn: "stone_position (l_states ! (length l_states - 1)) stone = n"
        using stone_positionI[of n "l_states ! (length l_states - 1)" stone n]
        using \<open>stone \<in> set [0..<n]\<close> \<open>l_states \<noteq> []\<close>
        using \<open>valid_labeled_game_max_stone n l_states\<close>
        using last_conv_nth[of l_states, symmetric]
        using valid_labeled_state_final_labeled_state
        unfolding valid_labeled_game_max_stone_def final_labeled_state_def
        by (simp del: replicate_Suc)

      have "n > 0"
        using \<open>length (?sstone stone) * (stone + 1) < n\<close> gr_implies_not0
        by blast

      have "length ss \<ge> 1"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "?sstone stone = []"
          using ss
          by (metis One_nat_def Suc_leI length_greater_0_conv)

        have "valid_labeled_moves n l_states"
          using \<open>valid_labeled_game_max_stone n l_states\<close>
          unfolding valid_labeled_game_max_stone_def
          using assms valid_labeled_game_def valid_labeled_game_max_stone_valid_labeled_game
          by blast

        then obtain p2 k where "k < length l_states - 1"
             "(0, p2, stone) = labeled_move_positions (l_states ! k) (l_states ! (k + 1))"
          using moved_from[of n l_states 0 "length l_states - 1" stone]
          using pos0 posn \<open>n > 0\<close> \<open>stone \<in> set [0..<n]\<close>
          using \<open>valid_labeled_game_max_stone n l_states\<close>
          unfolding valid_labeled_game_max_stone_def
          by force
        moreover
        have "(l_states ! k, l_states ! (k+1)) \<in> set (zip (butlast l_states) (tl l_states))"
          using \<open>k < length l_states - 1\<close> \<open>length l_states \<ge> 2\<close>
          by (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right in_set_conv_nth length_butlast length_tl length_zip min_less_iff_conj nth_butlast nth_tl nth_zip)
        ultimately
        have "(l_states ! k, 0, p2, stone) \<in> set (?sstone stone)"
          by auto
        then show False
          using \<open>?sstone stone = []\<close>
          by auto
      qed
      then have "ss \<noteq> []"
        by auto

      have "n = (\<Sum> (state, p1, p2, stone) \<leftarrow> ?sstone stone. p2 - p1)"
      proof-
        let ?p2p1 = "\<lambda> i. case ss ! i of (state, p1, p2, stone) \<Rightarrow> int p2 - int p1"
        let ?p1 = "\<lambda> i. case ss ! i of (state, p1, p2, stone) \<Rightarrow> int p1"
        let ?p2 = "\<lambda> i. case ss ! i of (state, p1, p2, stone) \<Rightarrow> int p2"

        have "(\<Sum> (state, p1, p2, stone) \<leftarrow> ss. p2 - p1) = 
              (\<Sum> (state, p1, p2, stone) \<leftarrow> ss. int (p2 - p1))"
        proof-
          have "(\<Sum> (state, p1, p2, stone) \<leftarrow> ss. p2 - p1) = 
                (\<Sum> x \<leftarrow> map (\<lambda> (state, p1, p2, stone). p2 - p1) ss. int x)"
            by (metis (no_types) map_nth sum_list_comp sum_list_int)
          also have "... = (\<Sum>(state, p1, p2, stone)\<leftarrow>ss. int (p2 - p1))"
          proof-
            have *: "(map int (map (\<lambda> (state, p1, p2, stone). p2 - p1) ss)) = 
                     (map (\<lambda> (state, p1, p2, stone). int (p2 - p1)) ss)"
              by auto
            show ?thesis
              by (subst *, simp)
          qed
          finally show ?thesis
            .
        qed
        also have "... = (\<Sum> (state, p1, p2, stone) \<leftarrow> ss. int p2 - int p1)"
        proof-
          have "\<forall> (state, p1, p2, stone) \<in> set ss. p2 \<ge> p1"
            using valid_moves'
            unfolding valid_labeled_move'_def Let_def
            by auto
          then have "\<forall> (state, p1, p2, stone) \<in> set ss. int (p2 - p1) = int p2 - int p1"
            by auto
          then have *: "map (\<lambda> (state, p1, p2, stone). int (p2 - p1)) ss = 
                 map (\<lambda> (state, p1, p2, stone). int p2 - int p1) ss"
            by auto
          show ?thesis
            by (subst *, simp)
        qed
        also have "... =  (\<Sum> i \<leftarrow> [0..<length ss]. ?p2p1 i)"
          by (metis (no_types) map_nth sum_list_comp)
        also have "... = (\<Sum> i \<leftarrow> [0..<length ss]. ?p2 i) -
                         (\<Sum> i \<leftarrow> [0..<length ss]. ?p1 i)"
        proof-
          have "\<forall> i \<in> set [0..<length ss]. ?p2p1 i = ?p2 i - ?p1 i"
            by (auto split: prod.split)
          then have "map ?p2p1 [0..<length ss] = map (\<lambda> i. ?p2 i - ?p1 i) [0..<length ss]"
            by auto
          then show ?thesis
            unfolding Let_def
            by (subst sum_list_subtractf[symmetric], presburger)
        qed
        also have "... = (\<Sum> i \<leftarrow> [0..<length ss-1]. ?p2 i) -
                         (\<Sum> i \<leftarrow> [1..<length ss]. ?p1 i) + (?p2 (length ss-1)) - (?p1 0)"
        proof-
          have "[0..<length ss] = [0..<length ss-1] @ [length ss - 1]"
               "[0..<length ss] = [0] @ [1..<length ss]"
            using \<open>length ss \<ge> 1\<close>
            by (metis le_add_diff_inverse plus_1_eq_Suc upt_Suc_append zero_le, 
                metis (mono_tags, lifting) One_nat_def le_add_diff_inverse less_numeral_extra(4) upt_add_eq_append upt_rec zero_le_one zero_less_one)
          then show ?thesis
            using sum_list_append
            by (smt list.map(1) list.map(2) map_append sum_list_simps(2))
        qed
        finally 
        have "(\<Sum> (state, p1, p2, stone) \<leftarrow> ss. p2 - p1) = 
                (\<Sum> i \<leftarrow> [0..<length ss-1]. ?p2 i) -
                (\<Sum> i \<leftarrow> [1..<length ss]. ?p1 i) + (?p2 (length ss-1)) - (?p1 0)"
          .
        moreover

        let ?P = "\<lambda>(state, p1, p2, stone'). stone' = stone"

        have "(\<Sum> i \<leftarrow> [1..<length ss]. ?p1 i) = (\<Sum> i \<leftarrow> [0..<length ss - 1]. ?p2 i)"
        proof-
          have *: "\<forall> i. 0 < i \<and> i < length ss \<longrightarrow> ?p1 i = ?p2 (i-1)"
          proof safe
            fix i 
            assume "0 < i" "i < length ss"
            show "?p1 i = ?p2 (i-1)"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              obtain k1 k2 where 
                "k1 < k2" "k2 < length ?ss"
                "ss ! (i-1) = ?ss ! k1" "ss ! i = ?ss ! k2"
                "?P (?ss ! k1)" "?P (?ss ! k2)" "\<forall> k'. k1 < k' \<and> k' < k2 \<longrightarrow> \<not> ?P (?ss ! k')"
                using ss inside_filter[of "i-1" ?P ?ss] \<open>0 < i\<close> \<open>i < length ss\<close>
                using \<open>ss \<noteq> []\<close> \<open>length l_states \<ge> 2\<close>
                by force
              have "k2 < length l_states"
                using \<open>k2 < length ?ss\<close>
                by simp
              have "?ss ! k1 = (l_states ! k1, labeled_move_positions (l_states ! k1) (l_states ! (k1+1)))"
                   "?ss ! k2 = (l_states ! k2, labeled_move_positions (l_states ! k2) (l_states ! (k2+1)))"
                using \<open>k1 < k2\<close> \<open>k2 < length ?ss\<close> \<open>length l_states \<ge> 2\<close>
                by (auto simp add: nth_butlast nth_tl)
              then obtain p1a p2a p1b p2b where
                "?ss ! k1 = (l_states ! k1, p1a, p2a, stone)" "labeled_move_positions (l_states ! k1) (l_states ! (k1+1)) = (p1a, p2a, stone)"
                "?ss ! k2 = (l_states ! k2, p1b, p2b, stone)" "labeled_move_positions (l_states ! k2) (l_states ! (k2+1)) = (p1b, p2b, stone)"
                using \<open>?P (?ss ! k1)\<close> \<open>?P (?ss ! k2)\<close>
                by auto
              then have "p2a \<noteq> p1b"
                using \<open>?p1 i \<noteq> ?p2 (i-1)\<close> \<open>ss ! (i-1) = ?ss ! k1\<close> \<open>ss ! i = ?ss ! k2\<close>
                by simp

              have "stone_position (l_states ! (k1 + 1)) stone \<noteq> stone_position (l_states ! k2) stone"
              proof-
                have "valid_labeled_state n (l_states ! k1)"
                  by (meson \<open>k1 < k2\<close> \<open>k2 < length l_states\<close> assms less_imp_le_nat less_le_trans nth_mem valid_labeled_game_max_stone_valid_labeled_game valid_labeled_game_valid_labeled_states)
                moreover
                then have "valid_labeled_move' n p1a p2a stone (l_states ! k1) (l_states ! (k1+1))"
                  using \<open>labeled_move_positions (l_states ! k1) (l_states ! (k1+1)) = (p1a, p2a, stone)\<close>
                  using labeled_move_positions_valid_move'
                  using \<open>k1 < k2\<close> \<open>k2 < length l_states\<close> \<open>valid_labeled_moves n l_states\<close> valid_labeled_moves_def
                  by auto
                ultimately
                have "stone_position (l_states ! (k1 + 1)) stone = p2a"
                  using valid_labeled_move'_stone_positions
                  by blast

                have "valid_labeled_state n (l_states ! k2)"
                  by (meson \<open>k2 < length l_states\<close> assms less_imp_le_nat less_le_trans nth_mem valid_labeled_game_max_stone_valid_labeled_game valid_labeled_game_valid_labeled_states)
                moreover
                then have "valid_labeled_move' n p1b p2b stone (l_states ! k2) (l_states ! (k2+1))"
                  using \<open>labeled_move_positions (l_states ! k2) (l_states ! (k2+1)) = (p1b, p2b, stone)\<close>
                  using labeled_move_positions_valid_move'
                  using \<open>k2 < length ?ss\<close>  \<open>valid_labeled_moves n l_states\<close> valid_labeled_moves_def
                  by (smt length_butlast length_map length_tl length_zip min_less_iff_conj)
                ultimately
                have "stone_position (l_states ! k2) stone = p1b"
                  using valid_labeled_move'_stone_positions
                  by blast

                show ?thesis
                  using \<open>stone_position (l_states ! k2) stone = p1b\<close>
                  using \<open>stone_position (l_states ! (k1 + 1)) stone = p2a\<close>
                  using \<open>p2a \<noteq> p1b\<close>
                  by simp
              qed
              then have "k1 + 1 < k2"
                using \<open>k1 < k2\<close>
                by (metis Suc_eq_plus1 Suc_leI nat_less_le)
              then obtain k' p1'' p2'' where "k1 + 1 \<le> k'" "k' < k2"
                "(p1'', p2'', stone) = labeled_move_positions (l_states ! k') (l_states ! (k' + 1))"
                using \<open>stone_position (l_states ! (k1 + 1)) stone \<noteq> stone_position (l_states ! k2) stone\<close>
                using moved_from[of n l_states "k1+1" "k2" stone] \<open>stone \<in> set [0..<n]\<close>
                using \<open>length l_states \<ge> 2\<close> \<open>k1 < k2\<close> \<open>k2 < length l_states\<close>
                using \<open>valid_labeled_moves n l_states\<close> \<open>valid_labeled_state n (hd l_states)\<close>
                by auto
              then have "?ss ! k' = (l_states ! k', p1'', p2'', stone)"
                using \<open>k2 < length ?ss\<close>
                by (auto simp add: nth_butlast nth_tl)
              then show False
                using \<open>\<forall> k'. k1 < k' \<and> k' < k2 \<longrightarrow> \<not> ?P (?ss ! k')\<close>[rule_format, of k'] \<open>k1 + 1 \<le> k'\<close> \<open>k' < k2\<close>
                by simp
            qed
          qed
          have "map ?p1 [1..<length ss] = map ?p2 [0..<length ss - 1]" (is "?lhs = ?rhs")
          proof (rule nth_equalityI)
            show "length ?lhs = length ?rhs"
              by simp
          next
            fix i
            assume "i < length ?lhs"
            then show "?lhs ! i = ?rhs ! i"
              using *
              by simp
          qed
          then show ?thesis
            by simp
        qed
        moreover
        have "?p2 (length ss - 1) = n"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          obtain k where 
            "k < length ?ss" "ss ! (length ss - 1) = ?ss ! k" "?P (?ss ! k)" "\<forall> k'. k < k' \<and> k' < length ?ss \<longrightarrow>  \<not> ?P (?ss ! k')"
            using ss last_filter[of ?P ?ss]
            using \<open>ss \<noteq> []\<close> \<open>length l_states \<ge> 2\<close>
            by auto
          have  "k < length l_states - 1"
            using \<open>k < length ?ss\<close>
            by simp
          have "?ss ! k = (l_states ! k, labeled_move_positions (l_states ! k) (l_states ! (k+1)))"
            using \<open>k < length ?ss\<close> \<open>length l_states \<ge> 2\<close>
            by (auto simp add: nth_butlast nth_tl)
          then obtain p1' p2' where "?ss ! k = (l_states ! k, p1', p2', stone)" "labeled_move_positions (l_states ! k) (l_states ! (k+1)) = (p1', p2', stone)"
            using \<open>?P (?ss ! k)\<close>
            by auto
          then have "p2' \<noteq> n"
            using \<open>?p2 (length ss - 1) \<noteq> n\<close> \<open>ss ! (length ss - 1) = ?ss ! k\<close>
            by auto
          have "stone_position (l_states ! (k + 1)) stone \<noteq> n"
          proof-
            have "stone_position (l_states ! (k + 1)) stone = p2'"
            proof-
              have "valid_labeled_move' n p1' p2' stone (l_states ! k) (l_states ! (k+1))"
                using \<open>labeled_move_positions (l_states ! k) (l_states ! (k+1)) = (p1', p2', stone)\<close>
                using \<open>k < length l_states - 1\<close> \<open>valid_labeled_moves n l_states\<close> \<open>valid_labeled_state n (hd l_states)\<close> 
                by (meson add_lessD1 labeled_move_positions_valid_move' less_diff_conv nth_mem valid_labeled_moves_def valid_labeled_moves_valid_labeled_states)
              moreover
              have "valid_labeled_state n (l_states ! k)"
                using \<open>k < length l_states - 1\<close> \<open>valid_labeled_moves n l_states\<close> \<open>valid_labeled_state n (hd l_states)\<close> 
                using valid_labeled_moves_valid_labeled_states
                by auto
              ultimately
              show ?thesis
                using valid_labeled_move'_stone_positions
                by blast
            qed
            then show ?thesis
              using \<open>p2' \<noteq> n\<close>
              by simp
          qed
          then have "k + 1 < length l_states - 1"
            using posn \<open>k < length l_states - 1\<close>
            by (smt Nat.le_diff_conv2 Nat.le_imp_diff_is_add Suc_leI add.right_neutral add_Suc_right add_leD2 diff_diff_left nat_less_le one_add_one plus_1_eq_Suc)
          then obtain k' p1'' p2'' where "k' \<ge> k + 1" "k' < length l_states - 1" "(p1'', p2'', stone) = labeled_move_positions (l_states ! k') (l_states ! (k' + 1))"
            using moved_from[of n l_states "k+1" "length l_states - 1" stone] 
            using posn \<open>stone_position (l_states ! (k+1)) stone \<noteq> n\<close> \<open>stone \<in> set [0..<n]\<close>
            using \<open>length l_states \<ge> 2\<close>
            using \<open>valid_labeled_moves n l_states\<close> \<open>valid_labeled_state n (hd l_states)\<close>
            by force
          then have "?ss ! k' = (l_states ! k', p1'', p2'', stone)"
            by (simp add: nth_butlast nth_tl)
          then show False
            using \<open>\<forall> k'. k < k' \<and> k' < length ?ss \<longrightarrow> \<not> ?P (?ss ! k')\<close>[rule_format, of k'] \<open>k' \<ge> k + 1\<close> \<open>k' < length l_states - 1\<close>
            by auto
        qed
        moreover
        have "?p1 0 = 0"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          obtain k where 
            "k < length ?ss" "ss ! 0 = ?ss ! k" "?P (?ss ! k)" "\<forall> k' < k. \<not> ?P (?ss ! k')"
            using ss hd_filter[of ?P ?ss]
            using \<open>ss \<noteq> []\<close> \<open>length l_states \<ge> 2\<close>
            by auto
          have  "k < length l_states - 1"
            using \<open>k < length ?ss\<close>
            by simp
          have "?ss ! k = (l_states ! k, labeled_move_positions (l_states ! k) (l_states ! (k+1)))"
            using \<open>k < length ?ss\<close> \<open>length l_states \<ge> 2\<close>
            by (auto simp add: nth_butlast nth_tl)
          then obtain p1' p2' where "?ss ! k = (l_states ! k, p1', p2', stone)" "labeled_move_positions (l_states ! k) (l_states ! (k+1)) = (p1', p2', stone)"
            using \<open>?P (?ss ! k)\<close>
            by auto
          then have "p1' \<noteq> 0"
            using \<open>?p1 0 \<noteq> 0\<close> \<open>ss ! 0 = ?ss ! k\<close>
            by auto
          have "stone_position (l_states ! k) stone \<noteq> 0"
          proof-
            have "valid_labeled_state n (l_states ! k)"
              by (meson \<open>k < length l_states - 1\<close> add_lessD1 assms less_diff_conv nth_mem valid_labeled_game_max_stone_valid_labeled_game valid_labeled_game_valid_labeled_states)
            moreover
            then have "valid_labeled_move' n p1' p2' stone (l_states ! k) (l_states ! (k+1))"
              using \<open>labeled_move_positions (l_states ! k) (l_states ! (k+1)) = (p1', p2', stone)\<close>
              using \<open>k < length l_states - 1\<close> \<open>valid_labeled_moves n l_states\<close> labeled_move_positions_valid_move' valid_labeled_moves_def
              by blast
            ultimately
            have "stone_position (l_states ! k) stone = p1'"
              using valid_labeled_move'_stone_positions
              by blast
            then show ?thesis
              using \<open>p1' \<noteq> 0\<close>
              by simp
          qed
          then have "k > 0"
            using pos0
            using neq0_conv
            by blast
          have "k < length l_states"
            using \<open>k < length l_states - 1\<close> \<open>length l_states \<ge> 2\<close> 
            by auto
          then obtain k' p2'' where "k' < k" "labeled_move_positions (l_states ! k') (l_states ! (k' + 1)) = (0, p2'', stone)"
            using moved_from[of n l_states 0 k stone] pos0 \<open>stone_position (l_states ! k) stone \<noteq> 0\<close>
            using \<open>valid_labeled_state n (hd l_states)\<close> \<open>valid_labeled_moves n l_states\<close> \<open>k > 0\<close> \<open>stone \<in> set [0..<n]\<close>
            by auto
          then have "?ss ! k' = (l_states ! k', 0, p2'', stone)"
            using \<open>k' < k\<close> \<open>k < length l_states - 1\<close>
            using \<open>k < length ?ss\<close> \<open>length l_states \<ge> 2\<close>
            by (auto simp add: nth_butlast nth_tl)
          then show False
            using \<open>\<forall> k' < k. \<not> ?P (?ss ! k')\<close>[rule_format, of k'] \<open>k' < k\<close>
            by simp
        qed
        ultimately
        show ?thesis
          using ss
          by simp
      qed
      also have "... \<le> (\<Sum> (state, p1, p2, stone) \<leftarrow> ?sstone stone. stone + 1)"
      proof (rule sum_list_mono)
        fix x :: "labeled_state \<times> nat \<times> nat \<times> nat"
        obtain state p1 p2 stone' where x: "x = (state, p1, p2, stone')"
          by (cases x)
        assume "x \<in> set (?sstone stone)"
        then have "x \<in> set ss"
          using ss
          by auto
        then obtain state' where "stone' = Max (state ! p1)" "valid_labeled_move' n p1 p2 (Max (state ! p1)) state state'"
          using x valid_moves'
          by auto
        then have "p1 < p2" "p2 \<le> p1 + card (state ! p1)"
          unfolding valid_labeled_move'_def Let_def
          by auto

        moreover

        have "card (state ! p1) \<le> Max (state ! p1) + 1"
          by (rule card_Max)

        ultimately

        show "(case x of (state, p1, p2, stone) \<Rightarrow> p2 - p1) \<le> 
              (case x of (state, p1, p2, stone) \<Rightarrow> stone + 1)"
          using x \<open>stone' = Max (state ! p1)\<close>
          by simp
      qed
      also have "... = (\<Sum> x \<leftarrow> ?sstone stone. stone + 1)"
      proof-                                               
        have "map (\<lambda> (state, p1, p2, stone). stone + 1) (?sstone stone) = 
              map (\<lambda> x. stone + 1) (?sstone stone)"
          by auto
        then show ?thesis
          by presburger
      qed
      also have "... = length (?sstone stone) * (stone + 1)"
        by (simp add: sum_list_triv)
      finally
      show False
        using \<open>length (?sstone stone) * (stone + 1) < n\<close>
        by simp
    qed
  qed
  also have "... \<le> length ?ss"
  proof-
    let ?ps = "map (\<lambda> stone. (\<lambda>(state, p1, p2, stone'). stone' = stone)) [0..<n]"
    have "\<forall> i j. i < j \<and> j < length ?ps \<longrightarrow> set (filter (?ps ! i) ?ss) \<inter> set (filter (?ps ! j) ?ss) = {}"
      by auto
    then have "(\<Sum> stone \<leftarrow> [0..<n]. length (?sstone stone)) \<le> length ?ss" 
      using sum_length_parts[of ?ps ?ss]
      by (auto simp add: comp_def split: prod.split)
    then show ?thesis
      by (subst sum_list_int, simp)
  qed
  finally 
  have "(\<Sum> k \<leftarrow> [1..<n+1]. (ceiling (n / k))) + 1 \<le> length ?ss + 1"
    by simp
  moreover
  have "length ?ss + 1 = length l_states"
    using \<open>l_states \<noteq> []\<close>
    by simp
  ultimately
  show ?thesis
    by simp
qed

subsubsection \<open>Valid game length\<close>

theorem IMO2018SL_C3:
  assumes "valid_game n states"
  shows "length states \<ge> (\<Sum> k \<leftarrow> [1..<n+1]. (ceiling (n / k))) + 1"
proof-
  let ?l_states = "label_moves_max_stone (initial_labeled_state n) (tl states)"
  have "length ?l_states = length states"
    using assms
    unfolding valid_game_def
    by auto
  moreover
  have "valid_labeled_game_max_stone n ?l_states"
    using valid_labeled_game_max_stone[OF assms]
    by simp
  ultimately
  show ?thesis
    using valid_labeled_game_max_stone_min_length[of n ?l_states]
    by simp
qed

end
