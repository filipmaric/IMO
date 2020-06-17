section \<open> Combinatorics problems \<close>

subsection \<open>IMO 2018 SL - C2\<close>

theory IMO_2018_SL_C2
imports Complex_Main
begin

locale dim = 
  fixes files :: int
  fixes ranks :: int
  assumes pos: "files > 0 \<and> ranks > 0"
  assumes div4: "files mod 4 = 0 \<and> ranks mod 4 = 0"
begin

type_synonym square = "int \<times> int"

definition squares :: "square set" where
  "squares = {0..<files} \<times> {0..<ranks}"

datatype piece = Queen | Knight

type_synonym board = "square \<Rightarrow> piece option"

definition empty_board :: board where
  "empty_board = (\<lambda> square. None)"

fun attacks_knight :: "square \<Rightarrow> board \<Rightarrow> bool" where
  "attacks_knight (file, rank) board \<longleftrightarrow> 
     (\<exists> file' rank'. (file', rank') \<in> squares \<and> board (file', rank') = Some Knight \<and> 
                     ((abs (file - file') = 1 \<and> abs (rank - rank') = 2) \<or>
                      (abs (file - file') = 2 \<and> abs (rank - rank') = 1)))"

definition valid_horst_move' :: "square \<Rightarrow> board \<Rightarrow> board \<Rightarrow> bool" where
  "valid_horst_move' square board board' \<longleftrightarrow> 
       square \<in> squares \<and> board square = None \<and>
       \<not> attacks_knight square board \<and> 
       board' = board (square := Some Knight)"

definition valid_horst_move :: "board \<Rightarrow> board \<Rightarrow> bool" where
  "valid_horst_move board board' \<longleftrightarrow> 
     (\<exists> square. valid_horst_move' square board board')"

definition valid_queenie_move :: "board \<Rightarrow> board \<Rightarrow> bool" where
  "valid_queenie_move board board' \<longleftrightarrow> 
     (\<exists> square \<in> squares. board square = None \<and> 
                          board' = board (square := Some Queen))"

type_synonym strategy = "board \<Rightarrow> board \<Rightarrow> bool"

inductive valid_game :: "strategy \<Rightarrow> strategy \<Rightarrow> nat \<Rightarrow> board \<Rightarrow> bool" where
  "valid_game horst_strategy queenie_strategy 0 empty_board"
| "\<lbrakk>valid_game horst_strategy queenie_strategy k board; 
    valid_horst_move board board'; horst_strategy board board';
    valid_queenie_move board' board''; queenie_strategy board' board''\<rbrakk>\<Longrightarrow> valid_game horst_strategy queenie_strategy (k + 1) board''"

definition valid_queenie_strategy :: "strategy \<Rightarrow> bool" where
  "valid_queenie_strategy queenie_strategy \<longleftrightarrow> 
     (\<forall>  horst_strategy board board' k. 
         valid_game horst_strategy queenie_strategy k board \<and>
         valid_horst_move board board' \<and> horst_strategy board board' \<and>
         (\<exists> square \<in> squares. board' square = None) \<longrightarrow> 
            (\<exists> board''. valid_queenie_move board' board'' \<and> queenie_strategy board' board''))"

(*
text \<open>squares\<close>
lemma squares_card [simp]:
  shows "card squares = files * ranks"
sorry

lemma squares_finite [simp]:
  shows "finite squares"
sorry

text \<open>\<open>free_squares\<close>\<close>

definition free_squares :: "board \<Rightarrow> square set" where
  "free_squares board = {square \<in> squares. board square = None}"

lemma free_squares_finite [simp]:
  shows "finite (free_squares board)"
sorry

lemma valid_game_free_squares_card_even:
  assumes "valid_game horst_strategy queenie_strategy k board"
  shows "card (free_squares board) mod 2 = 0"
sorry 

text \<open>black squares\<close>

fun black :: "square \<Rightarrow> bool" where
 "black (file, rank) \<longleftrightarrow> (file + rank) mod 2 = 0"

definition black_squares :: "square set" where
  "black_squares = {square \<in> squares. black square}"

lemma black_squares_finite [simp]:
  shows "finite black_squares"
sorry

lemma black_squares_card:
  "card black_squares = (files * ranks) div 2"
sorry

text \<open>free black squares\<close>

definition free_black_squares :: "board \<Rightarrow> square set" where
  "free_black_squares board = {square \<in> squares. black square \<and> board square = None}"

lemma free_black_squares_add_piece:
  shows "card (free_black_squares board) \<le> card (free_black_squares (board (square := Some piece))) + 1"
sorry

lemma free_black_squares_valid_horst_move:
  assumes "valid_horst_move board board'"
  shows "card (free_black_squares board) \<le> card (free_black_squares board') + 1"
sorry

lemma free_black_squares_valid_queenie_move:
  assumes "valid_queenie_move board board'"
  shows "card (free_black_squares board) \<le> card (free_black_squares board') + 1"
sorry

text \<open>knights\<close>

definition knights :: "board \<Rightarrow> square set" where
  "knights board = {square \<in> squares. board square = Some Knight}"

lemma knights_finite [simp]:
  shows "finite (knights board)"
sorry

lemma knights_card_horst_move [simp]:
  assumes "valid_horst_move board board'"
  shows "card (knights board') = card (knights board) + 1"
sorry

lemma knights_card_queenie_move [simp]:
  assumes "valid_queenie_move board board'"
  shows "card (knights board') = card (knights board)"
sorry

lemma valid_game_knights_card [simp]:
  assumes "valid_game horst_strategy queenie_strategy k board"
  shows "card (knights board) = k"
sorry

text \<open>Cycles\<close>

fun cycle_opposite :: "square \<Rightarrow> square" where 
  "cycle_opposite (file, rank) = (4 * (file div 4) + (3 - file mod 4), 4 * (rank div 4) + (3 - rank mod 4))"

lemma cycle_opposite_cycle_opposite [simp]:
  shows "cycle_opposite (cycle_opposite square) = square"
  by (cases square) auto

lemma cycle_opposite_different [simp]:
  shows "cycle_opposite square \<noteq> square"
  by (cases square, simp, presburger)

lemma cycle_opposite_squares [simp]:
  shows "cycle_opposite square \<in> squares \<longleftrightarrow> square \<in> squares"
  using pos div4
  by (cases square) (simp add: squares_def, safe, presburger+)

fun cycle4 :: "square \<Rightarrow> int" where
  "cycle4 (x, y) = 
      (if x = 0 then y 
       else if x = 1 then (y + 2) mod 4
       else if x = 2 then (5 - y) mod 4
       else 3 - y)"

lemma cycle_lt_4: 
  assumes "0 \<le> x" "x < 4" "0 \<le> y" "y < 4"
  shows "0 \<le> cycle4 (x, y) \<and> cycle4 (x, y) < 4"
  using assms
  by auto

lemma cycle0:
  assumes "0 \<le> x" "x < 4" "0 \<le> y" "y < 4"
  shows "cycle4 (x, y) = 0 \<longleftrightarrow> (x, y) \<in> set [(0, 0), (2, 1), (1, 2), (3, 3)]"
  using assms
  by auto presburger+

lemma cycle1:
  assumes "0 \<le> x" "x < 4" "0 \<le> y" "y < 4"
  shows "cycle4 (x, y) = 1 \<longleftrightarrow> (x, y) \<in> set [(0, 1), (1, 3), (3, 2), (2, 0)]"
  using assms
  by auto presburger+

lemma cycle2:
  assumes "0 \<le> x" "x < 4" "0 \<le> y" "y < 4"
  shows "cycle4 (x, y) = 2 \<longleftrightarrow> (x, y) \<in> set [(0, 2), (2, 3), (1, 0), (3, 1)]"
  using assms
  by auto presburger+

lemma cycle3:
  assumes "0 \<le> x" "x < 4" "0 \<le> y" "y < 4"
  shows "cycle4 (x, y) = 3 \<longleftrightarrow> (x, y) \<in> set [(0, 3), (1, 1), (2, 2), (3, 0)]"
  using assms
  by auto presburger+

fun cycle :: "square \<Rightarrow> int \<times> int \<times> int" where
  "cycle (x, y) = (x div 4, y div 4, cycle4 (x mod 4, y mod 4))"

lemma cycles_card:
  shows "card (cycle ` squares) = (files * ranks) div 4"
sorry

lemma cycle4_exhausted:
  assumes "0 \<le> f1" "f1 < 4" "0 \<le> r1" "r1 < 4" 
  assumes "0 \<le> f2" "f2 < 4" "0 \<le> r2" "r2 < 4" 
  assumes "(f1, r1) \<noteq> (f2, r2)" 
          "abs (f1 - f2) \<noteq> 1 \<or> abs (r1 - r2) \<noteq> 2"
          "abs (f1 - f2) \<noteq> 2 \<or> abs (r1 - r2) \<noteq> 1"
          "(f2, r2) \<noteq> (3 - f1, 3 - r1)"
  shows "cycle4 (f1, r1) \<noteq> cycle4 (f2, r2)"
sorry

lemma cycle_exhausted:
  assumes "\<forall> sq \<in> squares. board sq = Some Knight \<longrightarrow> \<not> attacks_knight sq board"
          "\<forall> sq \<in> squares. board sq = Some Knight \<longrightarrow> board (cycle_opposite sq) = Some Queen"
          "sq1 \<noteq> sq2" "sq1 \<in> squares" "sq2 \<in> squares" "board sq1 = Some Knight" "board sq2 = Some Knight"
  shows "cycle sq1 \<noteq> cycle sq2"
sorry

text \<open>guaranteed game lengths\<close>
*)
definition guaranteed_game_lengths :: "nat set" where
  "guaranteed_game_lengths = {K. \<exists> horst_strategy. \<forall> queenie_strategy. valid_queenie_strategy queenie_strategy \<longrightarrow> (\<exists> board. valid_game horst_strategy queenie_strategy K board)}"
(*
lemma guaranteed_game_lengths_geq: 
  shows "nat ((files * ranks) div 4) \<in> guaranteed_game_lengths"
sorry

lemma valid_game_not_attacks_knight:
  assumes "valid_game horst_strategy queenie_strategy k board"
          "square \<in> squares" "board square = Some Knight" 
        shows "\<not> attacks_knight square board"
sorry

lemma guaranteed_game_lengths_leq:
  shows "\<forall> k \<in> guaranteed_game_lengths. k \<le> (files * ranks) div 4"
sorry

lemma guaranteed_game_lengths_finite: 
  shows "finite guaranteed_game_lengths"
sorry
*)
theorem IMO2018SL_C2:
  shows "Max guaranteed_game_lengths = nat ((files * ranks) div 4)"
  sorry
end

end