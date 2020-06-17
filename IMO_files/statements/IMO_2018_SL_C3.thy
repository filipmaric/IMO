subsection \<open>IMO 2018 SL - C3\<close>

theory IMO_2018_SL_C3
  imports Complex_Main
begin

(*
subsubsection \<open>General lemmas\<close>

lemma sum_list_int [simp]:
  fixes xs :: "nat list"
  shows "(\<Sum> x \<leftarrow> xs. int (f x)) = int (\<Sum> x \<leftarrow> xs. f x)"
  sorry

lemma sum_list_comp:
  shows "(\<Sum> x \<leftarrow> xs. f (g x)) = (\<Sum> x \<leftarrow> map g xs. f x)"
  sorry

lemma lt_ceiling_frac:
  assumes "x < ceiling (a / b)" "b > 0"
  shows "x * b < a"
  sorry

lemma subset_Max:
  fixes X :: "nat set"
  assumes "finite X"
  shows "X \<subseteq> {0..<Max X + 1}"
  using assms
  sorry

lemma card_Max:
  fixes X :: "nat set"
  shows "card X \<le> Max X + 1"
  sorry

lemma sum_length_parts:
  assumes "\<forall> i j. i < j \<and> j < length ps \<longrightarrow> set (filter (ps ! i) xs) \<inter> set (filter (ps ! j) xs) = {}"
  shows "sum_list (map (\<lambda> p. length (filter p xs)) ps) \<le> length xs"
  sorry

lemma hd_filter:
  assumes "filter P xs \<noteq> []"
  shows "\<exists> k. k < length xs \<and> (filter P xs) ! 0 = xs ! k \<and> P (xs ! k) \<and> (\<forall> k' < k. \<not> P (xs ! k'))"
  sorry

lemma last_filter:
  assumes "filter P xs \<noteq> []"
  shows "\<exists> k. k < length xs \<and> (filter P xs) ! (length (filter P xs) - 1) = xs ! k \<and> P (xs ! k) \<and> (\<forall> k'. k < k' \<and> k' < length xs \<longrightarrow> \<not> P (xs ! k'))"
  sorry

lemma filter_tl [simp]:
  "filter P (tl xs) = (if P (hd xs) then tl (filter P xs) else filter P xs)"
  sorry

lemma filter_dropWhile_not [simp]:
  shows "filter P (dropWhile (\<lambda>x. \<not> P x) xs) = filter P xs"
  sorry

lemma inside_filter:
  assumes "i + 1 < length (filter P xs)"
  shows "\<exists> k1 k2. k1 < k2 \<and> k2 < length xs \<and> 
                  (filter P xs) ! i = xs ! k1 \<and> 
                  (filter P xs) ! (i + 1) = xs ! k2 \<and> 
                  P (xs ! k1) \<and> P (xs ! k2) \<and> 
                  (\<forall> k'. k1 < k' \<and> k' < k2 \<longrightarrow> \<not> P (xs ! k'))"
  sorry

subsubsection \<open>Unlabeled states\<close>
*)
type_synonym state = "nat list"

definition initial_state :: "nat \<Rightarrow> state" where
  "initial_state n = (replicate (n + 1) 0) [0 := n]"

definition final_state :: "nat \<Rightarrow> state" where
  "final_state n = (replicate (n + 1) 0) [n := n]"
(*
definition valid_state :: "nat \<Rightarrow> state \<Rightarrow> bool" where
   "valid_state n state \<longleftrightarrow> length state = n + 1 \<and> sum_list state = n"
*)

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

(*
lemma valid_state_initial_state [simp]:
  shows "valid_state n (initial_state n)"
  sorry

lemma valid_move_valid_state:
  assumes "valid_state n state" "valid_move n state state'"
  shows "valid_state n state'"
  sorry

lemma valid_moves_Nil [simp]:
  shows "valid_moves n []"
  sorry

lemma valid_moves_Single [simp]:
  shows "valid_moves n [state]"
  sorry

lemma valid_moves_Cons [simp]:
  shows "valid_moves n (state1 # state2 # states) \<longleftrightarrow> 
         valid_move n state1 state2 \<and> valid_moves n (state2 # states)"
  sorry

lemma valid_moves_valid_states:
  assumes "valid_moves n states" "valid_state n (hd states)"
  shows "\<forall> state \<in> set states. valid_state n state"
  sorry

lemma valid_game_valid_states:
  assumes "valid_game n states"
  shows "\<forall> state \<in> set states. valid_state n state"
  sorry

definition move_positions where
  "move_positions state state' = 
    (THE (p1, p2). valid_move' (length state - 1) p1 p2 state state')"

lemma move_positions_unique:
  assumes "valid_state n state" "valid_move n state state'"
  shows "\<exists>! (p1, p2). valid_move' n p1 p2 state state'"
  sorry

lemma valid_move'_move_positions:
  assumes "valid_state n state" "valid_move' n p1 p2 state state'"
  shows "(p1, p2) = move_positions state state'"
  sorry

lemma move_positions_valid_move':
  assumes "valid_state n state" "valid_move n state state'"
          "(p1, p2) = move_positions state state'"
  shows "valid_move' n p1 p2 state state'"
  sorry

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
  sorry

lemma valid_labeled_state_final_labeled_state [simp]:
  shows "valid_labeled_state n (final_labeled_state n)"
  sorry

lemma valid_labeled_move_valid_labeled_state:
  assumes "valid_labeled_state n l_state" "valid_labeled_move n l_state l_state'"
  shows "valid_labeled_state n l_state'"
  sorry

lemma valid_labeled_moves_valid_labeled_states:
  assumes "valid_labeled_moves n l_states" "valid_labeled_state n (hd l_states)"
  shows "\<forall> state \<in> set l_states. valid_labeled_state n state"
  sorry

lemma valid_labeled_game_valid_labeled_states:
  assumes "valid_labeled_game n states"
  shows "\<forall> state \<in> set states. valid_labeled_state n state"
  sorry

definition labeled_move_positions where
  "labeled_move_positions state state' = 
       (THE (p1, p2, stone). valid_labeled_move' (length state - 1) p1 p2 stone state state')"

lemma labeled_move_positions_unique:
  assumes "valid_labeled_state n state" "valid_labeled_move n state state'"
  shows "\<exists>! (p1, p2, stone). valid_labeled_move' n p1 p2 stone state state'"
  sorry

lemma labeled_move_positions:
  assumes "valid_labeled_state n state" "valid_labeled_move' n p1 p2 stone state state'"
  shows "labeled_move_positions state state' = (p1, p2, stone)"
  sorry

lemma labeled_move_positions_valid_move':
  assumes "valid_labeled_state n state" "valid_labeled_move n state state'"
          "labeled_move_positions state state' = (p1, p2, stone)"
  shows "valid_labeled_move' n p1 p2 stone state state'"
  sorry

definition stone_position :: "labeled_state \<Rightarrow> nat \<Rightarrow> nat" where
  "stone_position l_state stone = 
     (THE k. k < length l_state \<and> stone \<in> l_state ! k)"

lemma stone_position_unique:
  assumes "valid_labeled_state n l_state" "stone < n"
  shows "\<exists>! k. k < length l_state \<and> stone \<in> l_state ! k"
  sorry

lemma stone_position:
  assumes "valid_labeled_state n l_state" "stone < n"
  shows "stone_position l_state stone \<le> n \<and> 
         stone \<in> l_state ! (stone_position l_state stone)"
  sorry

lemma stone_positionI:
  assumes "valid_labeled_state n l_state" "stone < n" 
          "k < length l_state" "stone \<in> l_state ! k"
  shows "stone_position l_state stone = k"
  sorry

lemma valid_labeled_move'_stone_positions:
  assumes "valid_labeled_state n l_state" "valid_labeled_move' n p1 p2 stone l_state l_state'"
  shows "stone_position l_state stone = p1 \<and> stone_position l_state' stone = p2"
  sorry

lemma valid_labeled_move'_stone_positions_other:
  assumes "valid_labeled_state n l_state" "valid_labeled_move' n p1 p2 stone l_state l_state'"
  shows "\<forall> stone'. stone' \<noteq> stone \<and> stone' < n \<longrightarrow> 
                     stone_position l_state' stone' = stone_position l_state stone'"
  sorry

subsubsection \<open>Unlabel\<close>

definition unlabel :: "labeled_state \<Rightarrow> state" where 
  "unlabel = map card"

lemma unlabel_initial [simp]:
  shows "unlabel (initial_labeled_state n) = initial_state n"
  sorry

lemma unlabel_final [simp]:
  shows "unlabel (final_labeled_state n) = final_state n"
  sorry

lemma unlabel_valid:
  assumes "valid_labeled_state n l_state"
  shows "valid_state n (unlabel l_state)"
  sorry

lemma unlabel_valid_move':
  assumes "valid_labeled_state n l_state" "valid_labeled_move' n p1 p2 stone l_state l_state'"
  shows "valid_move' n p1 p2 (unlabel l_state) (unlabel l_state') \<and> 
         unlabel l_state' = move p1 p2 (unlabel l_state)"
  sorry

lemma unlabel_valid_move:
  assumes "valid_labeled_state n l_state" "valid_labeled_move n l_state l_state'"
  shows "valid_move n (unlabel l_state) (unlabel l_state')"
  sorry

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
  sorry

lemma valid_labeled_game_max_stone_valid_labeled_game:
  assumes "valid_labeled_game_max_stone n states"
  shows "valid_labeled_game n states"
  sorry

lemma valid_labeled_move_move_max_stone:
  assumes "valid_labeled_state n l_state"
          "unlabel l_state = state" "valid_move' n p1 p2 state state'"
          "l_state' = labeled_move p1 p2 (Max (l_state ! p1)) l_state"
        shows "valid_labeled_move' n p1 p2 (Max (l_state ! p1)) l_state l_state'"
  sorry

primrec label_moves_max_stone where
  "label_moves_max_stone l_state [] = [l_state]"
| "label_moves_max_stone l_state (state' # states) = 
     (let state = unlabel l_state;
          (p1, p2) = move_positions state state';
          l_state' = labeled_move p1 p2 (Max (l_state ! p1)) l_state
       in l_state # label_moves_max_stone l_state' states)"

lemma hd_label_moves_max_stone [simp]:
  shows "hd (label_moves_max_stone l_state states) = l_state"
  sorry

lemma valid_states_label_moves_max_stone:
  assumes "valid_labeled_state n l_state" "valid_moves n (unlabel l_state # states)"
  shows "\<forall> l_state' \<in> set (label_moves_max_stone l_state states). valid_labeled_state n l_state'"
  sorry

lemma unlabel_label_moves_max_stone:
  assumes "valid_labeled_state n l_state"  "valid_moves n (unlabel l_state # states)"
  shows "map unlabel (label_moves_max_stone l_state states) = unlabel l_state # states"
  sorry

lemma label_moves_max_stone_length [simp]:
  shows "length (label_moves_max_stone l_state states) = length states + 1"
  sorry

lemma label_moves_max_stone_valid_moves:
  assumes "valid_labeled_state n l_state" "valid_moves n (unlabel l_state # states)"
  shows "valid_labeled_moves_max_stone n (label_moves_max_stone l_state states)"
  sorry

lemma final_labeled_state_unique:
  assumes "unlabel l_state = final_state n" "valid_labeled_state n l_state"
  shows "l_state = final_labeled_state n"
  sorry

lemma labeled_game_max_stone_length [simp]:
  assumes "valid_game n states"
  shows "length (label_moves_max_stone (initial_labeled_state n) (tl states)) = length states"
  sorry

lemma valid_labeled_game_max_stone:
  assumes "valid_game n states"
  shows "valid_labeled_game_max_stone n (label_moves_max_stone (initial_labeled_state n) (tl states))"
  sorry


subsubsection \<open>Valid labeled game move max stone length\<close>

lemma moved_from:
  assumes "valid_labeled_state n (hd l_states)" "valid_labeled_moves n l_states"
          "i < j" "j < length l_states" "stone < n"
          "stone_position (l_states ! i) stone \<noteq> stone_position (l_states ! j) stone"
  shows "(\<exists> k. i \<le> k \<and> k < j \<and> 
         (let (p1, p2, stone') = labeled_move_positions (l_states ! k) (l_states ! (k + 1)) in 
          stone' = stone \<and> p1 = stone_position (l_states ! i) stone))"
  sorry

lemma valid_labeled_game_max_stone_min_length:
  assumes "valid_labeled_game_max_stone n l_states"
  shows "length l_states \<ge> (\<Sum> k \<leftarrow> [1..<n+1]. (ceiling (n / k))) + 1"
  sorry

subsubsection \<open>Valid game length\<close>
*)
theorem IMO2018SL_C3:
  assumes "valid_game n states"
  shows "length states \<ge> (\<Sum> k \<leftarrow> [1..<n+1]. (ceiling (n / k))) + 1"
  sorry

end
