section \<open> Combinatorics problems \<close>

subsection \<open>IMO 2018 SL - C2\<close>

theory IMO_2018_SL_C2_sol
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


text \<open>squares\<close>
lemma squares_card [simp]:
  shows "card squares = files * ranks"
  using pos
  unfolding squares_def
  by auto

lemma squares_finite [simp]:
  shows "finite squares"
  using pos
  unfolding squares_def
  by auto

text \<open>\<open>free_squares\<close>\<close>

definition free_squares :: "board \<Rightarrow> square set" where
  "free_squares board = {square \<in> squares. board square = None}"

lemma free_squares_finite [simp]:
  shows "finite (free_squares board)"
proof (rule finite_subset)
  show "free_squares board \<subseteq> squares"
    by (simp add: free_squares_def)
qed simp

lemma valid_game_free_squares_card_even:
  assumes "valid_game horst_strategy queenie_strategy k board"
  shows "card (free_squares board) mod 2 = 0"
  using assms
proof (induction horst_strategy queenie_strategy k board rule: valid_game.induct)
  case (1 horst_strategy queenie_strategy)
  show ?case
  proof-
    have "card (free_squares empty_board) = files * ranks"
      by (simp add: empty_board_def free_squares_def)
    then show ?thesis
      using div4
      by presburger
  qed
next
  case (2 horst_strategy queenie_strategy K board board' board'')
  then obtain square square' where
    "square \<in> squares" "board square = None" "board' = board (square := Some Knight)"
    "square' \<in> squares" "board' square' = None" "board'' = board' (square' := Some Queen)"
    unfolding valid_horst_move_def valid_horst_move'_def valid_queenie_move_def
    by auto
  then have "free_squares board = free_squares board'' \<union> {square, square'}"
        "square \<notin> free_squares board''" "square' \<notin> free_squares board''"
    unfolding free_squares_def
    by (auto split: if_split_asm)
  moreover
  have "square \<noteq> square'"
    using \<open>board' = board(square \<mapsto> Knight)\<close> \<open>board' square' = None\<close>
    by auto
  ultimately
  have "card (free_squares board) = card (free_squares board'') + 2"
    using card_Un_disjoint[of "free_squares board''" "{square, square'}"]
    by auto
  then show ?case
    using \<open>card (free_squares board) mod 2 = 0\<close>
    by simp
qed

text \<open>black squares\<close>

fun black :: "square \<Rightarrow> bool" where
 "black (file, rank) \<longleftrightarrow> (file + rank) mod 2 = 0"

definition black_squares :: "square set" where
  "black_squares = {square \<in> squares. black square}"

lemma black_squares_finite [simp]:
  shows "finite black_squares"
  using pos
  unfolding black_squares_def
  by auto

lemma black_squares_card:
  "card black_squares = (files * ranks) div 2"
proof-
  let ?black_squares = "{square \<in> squares. black square}"
  let ?white_squares = "{square \<in> squares. \<not> black square}"
  have "squares = ?black_squares \<union> ?white_squares"
    by blast
  moreover
  have "?black_squares \<inter> ?white_squares = {}"
    by blast
  moreover
  have "card ?black_squares = card ?white_squares"
  proof-
    let ?f = "\<lambda> (a::int, b::int). if a mod 2 = 0 then (a, b + 1) else (a, b - 1)"
    have "bij_betw ?f ?black_squares ?white_squares"
      unfolding bij_betw_def
    proof
      show "inj_on ?f ?black_squares"
        unfolding inj_on_def
        by auto
    next
      show "?f ` ?black_squares = ?white_squares"
      proof
        show "?f ` ?black_squares \<subseteq> ?white_squares"
          using div4
          by (auto simp add: squares_def split: if_split_asm) presburger+
      next
        show "?white_squares \<subseteq> ?f ` ?black_squares"
        proof
          fix wsq
          assume "wsq \<in> ?white_squares"
          let ?invf = "\<lambda> (a, b). if a mod 2 = 0 then (a, b - 1) else (a, b + 1)"
          have "?f (?invf wsq) = wsq"
            by (cases wsq, auto)
          moreover
          have "?invf wsq \<in> ?black_squares"
            using \<open>wsq \<in> ?white_squares\<close> div4
            by (cases wsq, auto simp add: squares_def) presburger+
          ultimately
          show "wsq \<in> ?f ` ?black_squares"
            by force
        qed
      qed
    qed
    then show ?thesis
      using bij_betw_same_card by blast
  qed
  ultimately
  have "2 * card ?black_squares = card squares"
    by (metis (no_types, lifting) card.infinite card_Un_disjoint finite_Un mult_2 mult_eq_0_iff)
  then have "2 * card ?black_squares = files * ranks"
    by auto
  then show ?thesis
    unfolding black_squares_def
    by simp
qed

text \<open>free black squares\<close>

definition free_black_squares :: "board \<Rightarrow> square set" where
  "free_black_squares board = {square \<in> squares. black square \<and> board square = None}"

lemma free_black_squares_add_piece:
  shows "card (free_black_squares board) \<le> card (free_black_squares (board (square := Some piece))) + 1"
proof-
  let ?board' = "board (square := Some piece)"
  have "free_black_squares board = free_black_squares ?board' \<or>
        free_black_squares board = free_black_squares ?board' \<union> {square}"
    unfolding free_black_squares_def Let_def
    by auto
  then show ?thesis
    by (metis One_nat_def add.right_neutral add_Suc_right card.infinite card_Un_le card_empty card_insert_if finite_Un finite_insert insert_absorb insert_not_empty le_add1 trans_le_add2)
qed

lemma free_black_squares_valid_horst_move:
  assumes "valid_horst_move board board'"
  shows "card (free_black_squares board) \<le> card (free_black_squares board') + 1"
  using assms
  using free_black_squares_add_piece
  unfolding valid_horst_move_def valid_horst_move'_def free_black_squares_def
  by auto

lemma free_black_squares_valid_queenie_move:
  assumes "valid_queenie_move board board'"
  shows "card (free_black_squares board) \<le> card (free_black_squares board') + 1"
  using assms
  using free_black_squares_add_piece 
  unfolding valid_queenie_move_def free_black_squares_def
  by auto

text \<open>knights\<close>

definition knights :: "board \<Rightarrow> square set" where
  "knights board = {square \<in> squares. board square = Some Knight}"

lemma knights_finite [simp]:
  shows "finite (knights board)"
  by (rule finite_subset[of _ squares], simp_all add: knights_def)

lemma knights_card_horst_move [simp]:
  assumes "valid_horst_move board board'"
  shows "card (knights board') = card (knights board) + 1"
proof-
  obtain square where "square \<in> squares" "board square = None" "board' square = Some Knight"
    "board' = board (square := Some Knight)"
    using assms
    unfolding valid_horst_move_def valid_horst_move'_def
    by auto
  then have "knights board' = knights board \<union> {square}"
    unfolding knights_def
    by auto
  then show ?thesis
    using \<open>board square = None\<close>
    unfolding knights_def
    by auto
qed

lemma knights_card_queenie_move [simp]:
  assumes "valid_queenie_move board board'"
  shows "card (knights board') = card (knights board)"
proof-
  have "knights board' = knights board"
    using assms
    unfolding valid_queenie_move_def knights_def
    by force
  then show ?thesis
    by simp
qed

lemma valid_game_knights_card [simp]:
  assumes "valid_game horst_strategy queenie_strategy k board"
  shows "card (knights board) = k"
  using assms
proof (induction horst_strategy queenie_strategy k board rule: valid_game.induct)
  case (1 horst_strategy queenie_strategy)
  show ?case
    by (simp add: empty_board_def knights_def)
next
  case (2 horst_strategy queenie_strategy K board board' board'')
  then show ?case
    by auto
qed

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
proof-
  have "cycle ` squares = {(x, y, z). x \<in> {0..<files div 4} \<and> y \<in> {0..<ranks div 4} \<and> z \<in> {0..<4}}"
  proof safe
    fix f r x y z
    assume "(f, r) \<in> squares" "(x, y, z) = cycle (f, r)"
    then have "0 \<le> f \<and> f < files" "0 \<le> r \<and> r < ranks"
      by (auto simp add: squares_def)
    then have "0 \<le> f div 4 \<and> f div 4 < files div 4"  "0 \<le> r div 4 \<and> r div 4 < ranks div 4"
      using div4
      by presburger+
    then show "x \<in> {0..<files div 4}" "y \<in> {0..<ranks div 4}"
      using \<open>(x, y, z) = cycle (f, r)\<close>
      by auto
    show "z \<in> {0..<4}"
      using cycle_lt_4[rule_format, of "f mod 4" "r mod 4"]
      using \<open>(x, y, z) = cycle (f, r)\<close>
      by simp
  next
    fix x y z :: int
    assume *: "x \<in> {0..<files div 4}" "y \<in> {0..<ranks div 4}" "z \<in> {0..<4}"
    let ?f = "4 * x" and ?r = "4 * y + z"
    have "(?f, ?r) \<in> squares" "cycle (?f, ?r) = (x, y, z)"
      using *
      by (auto simp add: squares_def)
    then have "\<exists> square \<in> squares. cycle square = (x, y, z)"
      by blast
    then show "(x, y, z) \<in> cycle ` squares"
      by (metis imageI)
  qed
  also have "... = {0..<files div 4} \<times> {0..<ranks div 4} \<times> {0..<4}"
    by auto
  finally
  have "card (cycle ` squares) = (files div 4) * (ranks div 4) * 4" 
    using pos
    by simp
  also have "... = (files * ranks) div 4"
    using div4
    by auto
  finally show ?thesis
    .
qed

lemma cycle4_exhausted:
  assumes "0 \<le> f1" "f1 < 4" "0 \<le> r1" "r1 < 4" 
  assumes "0 \<le> f2" "f2 < 4" "0 \<le> r2" "r2 < 4" 
  assumes "(f1, r1) \<noteq> (f2, r2)" 
          "abs (f1 - f2) \<noteq> 1 \<or> abs (r1 - r2) \<noteq> 2"
          "abs (f1 - f2) \<noteq> 2 \<or> abs (r1 - r2) \<noteq> 1"
          "(f2, r2) \<noteq> (3 - f1, 3 - r1)"
  shows "cycle4 (f1, r1) \<noteq> cycle4 (f2, r2)"
  using assms cycle_lt_4[rule_format, of f1 r1]
  by (smt cycle0 cycle1 cycle2 cycle3 list.set_intros(1) list.set_intros(2))

lemma cycle_exhausted:
  assumes "\<forall> sq \<in> squares. board sq = Some Knight \<longrightarrow> \<not> attacks_knight sq board"
          "\<forall> sq \<in> squares. board sq = Some Knight \<longrightarrow> board (cycle_opposite sq) = Some Queen"
          "sq1 \<noteq> sq2" "sq1 \<in> squares" "sq2 \<in> squares" "board sq1 = Some Knight" "board sq2 = Some Knight"
  shows "cycle sq1 \<noteq> cycle sq2"
proof safe
  assume "cycle sq1 = cycle sq2"
  obtain f1 r1 where sq1: "sq1 = (f1, r1)"
    by (cases sq1)
  obtain f2 r2 where sq2: "sq2 = (f2, r2)"
    by (cases sq2)

  have **: "f1 div 4 = f2 div 4" "r1 div 4 = r2 div 4"
            "cycle4 (f1 mod 4, r1 mod 4) = cycle4 (f2 mod 4, r2 mod 4)"
    using \<open>cycle sq1 = cycle sq2\<close> sq1 sq2
    by simp_all

  have "\<not> attacks_knight (f1, r1) board" "(f2, r2) \<noteq> cycle_opposite (f1, r1)"
    using assms(1)[rule_format, of "(f1, r1)"] 
    using assms(2)[rule_format, of "(f1, r1)"]
    using assms(4-7) sq1 sq2
    by auto
  
  have "f2 \<noteq> 4 * (f1 div 4) + (3 - f1 mod 4) \<or> r2 \<noteq> 4 * (r1 div 4) + (3 - r1 mod 4)"
    using \<open>(f2, r2) \<noteq> cycle_opposite (f1, r1)\<close>
    by auto

  then have "f2 mod 4 \<noteq> 3 - f1 mod 4 \<or> r2 mod 4 \<noteq> 3 - r1 mod 4"
    using **(1-2)
    by safe presburger+

  then have 1: "(f2 mod 4, r2 mod 4) \<noteq> (3 - f1 mod 4, 3 - r1 mod 4)"
    by simp

  have "(\<bar>f1 - f2\<bar> = 1 \<longrightarrow> \<bar>r1 - r2\<bar> \<noteq> 2) \<and> (\<bar>f1 - f2\<bar> = 2 \<longrightarrow> \<bar>r1 - r2\<bar> \<noteq> 1)"
    using \<open>\<not> attacks_knight (f1, r1) board\<close>
    using assms attacks_knight.simps sq1 sq2
    by blast

  then have 2: "\<bar>f1 mod 4 - f2 mod 4\<bar> \<noteq> 1 \<or> \<bar>r1 mod 4 - r2 mod 4\<bar> \<noteq> 2"
               "\<bar>f1 mod 4 - f2 mod 4\<bar> \<noteq> 2 \<or> \<bar>r1 mod 4 - r2 mod 4\<bar> \<noteq> 1"
    using **(1-2)
    by (smt mult_div_mod_eq)+

  have "(f1 mod 4, r1 mod 4) = (f2 mod 4, r2 mod 4)"
    using **(3) cycle4_exhausted[OF _ _ _ _ _ _ _ _ _ 2 1]
    using pos_mod_conj zero_less_numeral
    by blast

  then have "f1 = f2" "r1 = r2"
    using **(1-2)
    by (metis mult_div_mod_eq prod.inject)+

  then show False
    using sq1 sq2 \<open>sq1 \<noteq> sq2\<close>
    by simp
qed

text \<open>guaranteed game lengths\<close>

definition guaranteed_game_lengths :: "nat set" where
  "guaranteed_game_lengths = {K. \<exists> horst_strategy. \<forall> queenie_strategy. valid_queenie_strategy queenie_strategy \<longrightarrow> (\<exists> board. valid_game horst_strategy queenie_strategy K board)}"

lemma guaranteed_game_lengths_geq: 
  shows "nat ((files * ranks) div 4) \<in> guaranteed_game_lengths"
  unfolding guaranteed_game_lengths_def
proof safe
  let ?l = "nat ((files * ranks) div 4)"
  let ?horst_strategy = "\<lambda> board board' :: board. (\<exists> square. black square \<and> valid_horst_move' square board board')"
  show "\<exists> horst_strategy. \<forall> queenie_strategy. valid_queenie_strategy queenie_strategy \<longrightarrow> (\<exists> board. valid_game horst_strategy queenie_strategy ?l board)"
  proof (rule_tac x="?horst_strategy" in exI, safe)
    fix queenie_strategy
    assume "valid_queenie_strategy queenie_strategy"

    have 1: "\<forall> k board. valid_game ?horst_strategy queenie_strategy k board \<longrightarrow> (\<forall> square \<in> squares. board square = Some Knight \<longrightarrow> black square)" (is "\<forall> k. ?P k")
    proof safe
      fix k board f r
      assume "valid_game ?horst_strategy queenie_strategy k board"
             "(f, r) \<in> squares" "board (f, r) = Some Knight"
      then show "black (f, r)"
      proof (induction ?horst_strategy queenie_strategy k board rule: valid_game.induct)
        case (1 queenie_strategy)
        then show ?case
          by (simp add: empty_board_def)
      next
        case (2 queenie_strategy K board board' board'')
        then show ?case
          by (smt map_upd_Some_unfold piece.simps(1) valid_horst_move'_def valid_queenie_move_def)
      qed
    qed

    have "\<forall> k \<le> (files * ranks) div 4. \<exists> board. valid_game ?horst_strategy queenie_strategy k board"
    proof safe
      fix k::nat
      assume "k \<le> (files * ranks) div 4"
      then show "\<exists> board. valid_game ?horst_strategy queenie_strategy k board"
      proof (induction k)
        case 0
        then show ?case
          by (rule_tac x=empty_board in exI, simp add: valid_game.intros)
      next
        case (Suc k)
        then obtain board where "valid_game ?horst_strategy queenie_strategy k board"
          by auto
        then have *: "(files * ranks) div 2 - 2 * k \<le> card (free_black_squares board)"
          using \<open>Suc k \<le> (files * ranks) div 4\<close>
        proof (induction ?horst_strategy queenie_strategy k board rule: valid_game.induct)
          case 1
          then show ?case
            using black_squares_card
            by (simp add: empty_board_def black_squares_def free_black_squares_def)
        next
          case (2 queenie_strategy k board board' board'')
          then have "(files * ranks) div 2 - 2 * k \<le> card (free_black_squares board)"
            by auto
          also have "... \<le> card (free_black_squares board') + 1"
            using 2
            using free_black_squares_valid_horst_move[of board board']
            by simp
          also have "... \<le> card (free_black_squares board'') + 2"
            using 2
            using free_black_squares_valid_queenie_move[of board' board'']
            by simp
          finally show ?case
            using \<open>Suc (k + 1) \<le> (files * ranks) div 4\<close>
            by (simp add: le_diff_conv)
        qed
        then have "card (free_black_squares board) > 0"
          using \<open>Suc k \<le> (files * ranks) div 4\<close>
          by auto
        then obtain square where "square \<in> free_black_squares board"
          by (metis Collect_empty_eq Collect_mem_eq card.infinite card_0_eq not_less0)

        have "\<not> attacks_knight square board"
        proof (rule ccontr)
          obtain x y where "square = (x, y)"
            by (cases square)
          assume "\<not> ?thesis"
          then obtain x' y' where "(x', y') \<in> squares" "board (x', y') = Some Knight" "\<bar>x - x'\<bar> = 1 \<and> \<bar>y - y'\<bar> = 2 \<or> \<bar>x - x'\<bar> = 2 \<and> \<bar>y - y'\<bar> = 1"
            using \<open>square = (x, y)\<close>
            by auto
          then have "black (x', y')"
            using 1[rule_format, OF \<open>valid_game ?horst_strategy queenie_strategy k board\<close>]
            by auto

          have "black (x, y)"
            using \<open>square \<in> free_black_squares board\<close> \<open>square = (x, y)\<close>
            by (simp add: free_black_squares_def)

          show False
            using \<open>black (x, y)\<close> \<open>black (x', y')\<close> \<open>\<bar>x - x'\<bar> = 1 \<and> \<bar>y - y'\<bar> = 2 \<or> \<bar>x - x'\<bar> = 2 \<and> \<bar>y - y'\<bar> = 1\<close>
            unfolding black.simps
            by presburger
        qed
          
        let ?board1 = "board (square := Some Knight)"
        have "valid_horst_move board ?board1"
          using \<open>square \<in> free_black_squares board\<close> \<open>\<not> attacks_knight square board\<close>
          unfolding valid_horst_move_def valid_horst_move'_def
          by (rule_tac x=square in exI, cases square, simp add: free_black_squares_def)

        moreover

        have "?horst_strategy board ?board1"
          using \<open>valid_horst_move board ?board1\<close> \<open>square \<in> free_black_squares board\<close>
          unfolding valid_horst_move_def free_black_squares_def
          by (rule_tac x=square in exI, cases square)
             (metis (mono_tags, lifting) map_upd_Some_unfold mem_Collect_eq option.discI valid_horst_move'_def)

        moreover

        have "\<exists> square \<in> squares. ?board1 square = None"
        proof-
          have "card (free_squares board) mod 2 = 0"
            using \<open>valid_game ?horst_strategy queenie_strategy k board\<close>
            using valid_game_free_squares_card_even 
            by blast
          have "free_squares board = free_squares ?board1 \<union> {square}" "square \<notin> free_squares ?board1"
            using \<open>square \<in> free_black_squares board\<close>
            unfolding free_black_squares_def free_squares_def
            by auto
          then have "card (free_squares board) = card (free_squares ?board1) + 1"
            by auto
          then have "card (free_squares ?board1) mod 2 = 1"
            using \<open>card (free_squares board) mod 2 = 0\<close>
            by presburger
          then have "free_squares ?board1 \<noteq> {}"
            by auto
          then show ?thesis
            unfolding free_squares_def
            by blast
        qed

        then obtain board2 where "valid_queenie_move ?board1 board2" "queenie_strategy ?board1 board2"
          using \<open>valid_queenie_strategy queenie_strategy\<close>
          unfolding valid_queenie_strategy_def
          using \<open>valid_game ?horst_strategy queenie_strategy k board\<close> calculation(1) calculation(2) valid_horst_move'_def 
          by blast

        ultimately

        show ?case
          using \<open>valid_game ?horst_strategy queenie_strategy k board\<close>
          by (metis (no_types, lifting) Suc_eq_plus1  valid_game.intros(2))
      qed
    qed
    then show "\<exists> board. valid_game ?horst_strategy queenie_strategy ?l board"
      using pos
      by simp
  qed
qed

lemma valid_game_not_attacks_knight:
  assumes "valid_game horst_strategy queenie_strategy k board"
          "square \<in> squares" "board square = Some Knight" 
        shows "\<not> attacks_knight square board"
  using assms
proof (induction horst_strategy queenie_strategy k board rule: valid_game.induct)
  case (1 horst_strategy queenie_strategy)
  then show ?case
    by (simp add: empty_board_def)
next
  case (2 horst_strategy queenie_strategy K board board' board'')
  have "\<not> attacks_knight square board'"
  proof (cases "board square = Some Knight")
    case True
    then have "\<not> attacks_knight square board"
      using 2
      by simp
    show ?thesis
    proof (rule ccontr)
      assume "\<not> ?thesis"
      obtain x y where "square = (x, y)"
        by (cases square)
      then obtain x' y' where "(x', y') \<in> squares" "board' (x', y') = Some Knight"
        "\<bar>x - x'\<bar> = 1 \<and> \<bar>y - y'\<bar> = 2 \<or> \<bar>x - x'\<bar> = 2 \<and> \<bar>y - y'\<bar> = 1"
        using \<open>\<not> \<not> attacks_knight square board'\<close> 
        by auto
      obtain square' where 
        "square' \<in> squares" "\<not> attacks_knight square' board"
        "board square' = None" "board' = board (square' := Some Knight)"
        using \<open>valid_horst_move board board'\<close>
        unfolding valid_horst_move_def valid_horst_move'_def
        by auto
      have "square' = (x', y')"
        using \<open>\<bar>x - x'\<bar> = 1 \<and> \<bar>y - y'\<bar> = 2 \<or> \<bar>x - x'\<bar> = 2 \<and> \<bar>y - y'\<bar> = 1\<close>
        using \<open>\<not> attacks_knight square board\<close> \<open>board' (x', y') = Some Knight\<close> \<open>board' = board(square' \<mapsto> Knight)\<close> \<open>(x', y') \<in> squares\<close> \<open>square = (x, y)\<close>
        by (metis (full_types)  attacks_knight.simps fun_upd_other)
      then have "attacks_knight square' board"
        using \<open>square' \<in> squares\<close>  \<open>\<bar>x - x'\<bar> = 1 \<and> \<bar>y - y'\<bar> = 2 \<or> \<bar>x - x'\<bar> = 2 \<and> \<bar>y - y'\<bar> = 1\<close>
              \<open>board square = Some Knight\<close> \<open>square = (x, y)\<close>
        using \<open>square \<in> squares\<close> \<open>board square = Some Knight\<close>
        by (smt attacks_knight.simps)
      then show False
        using \<open>\<not> attacks_knight square' board\<close>
        by simp
    qed
  next
    case False
    have "board' square = Some Knight"
      using \<open>square \<in> squares\<close> \<open>board'' square = Some Knight\<close> \<open>valid_queenie_move board' board''\<close>
      by (metis map_upd_Some_unfold piece.distinct(1) valid_queenie_move_def)

    obtain square' where *: "square' \<in> squares"
      "board square' = None" "\<not> attacks_knight square' board" 
      "board' = board(square' \<mapsto> Knight)"
      using \<open>valid_horst_move board board'\<close>
      unfolding valid_horst_move_def valid_horst_move'_def
      by blast
    then have "square = square'"
      using \<open>board square \<noteq> Some Knight\<close>
      using \<open>board' square = Some Knight\<close>
      by (metis fun_upd_apply)
    then have "\<not> attacks_knight square board"
      using \<open>\<not> attacks_knight square' board\<close>
      by simp
    then show ?thesis
      by (cases square) (simp add: "*"(4) \<open>square = square'\<close>)
  qed
  then show ?case
    using \<open>valid_queenie_move board' board''\<close>
    by (smt attacks_knight.elims(2) attacks_knight.elims(3) fun_upd_apply option.inject piece.simps(1) prod.simps(1) valid_queenie_move_def)
qed

lemma guaranteed_game_lengths_leq:
  shows "\<forall> k \<in> guaranteed_game_lengths. k \<le> (files * ranks) div 4"
proof safe
  fix k
  assume "k \<in> guaranteed_game_lengths"
  then obtain horst_strategy where
    *: "\<forall> queenie_strategy. valid_queenie_strategy queenie_strategy \<longrightarrow> 
                            (\<exists> board. valid_game horst_strategy queenie_strategy k board)"
    unfolding guaranteed_game_lengths_def
    by auto
  show "k \<le> (files * ranks) div 4"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "k > (files * ranks) div 4"
      by simp

    let ?queenie_strategy = "\<lambda> board board'. (\<exists> square \<in> squares. board square = Some Knight \<and> board (cycle_opposite square) = None \<and> board' (cycle_opposite square) = Some Queen)"

    have 1: "\<forall> k horst_strategy board. valid_game horst_strategy ?queenie_strategy k board \<longrightarrow> 
              (\<forall> square \<in> squares. board square = Some Knight \<longleftrightarrow> board (cycle_opposite square) = Some Queen)" (is "\<forall> k. ?P k")
    proof (rule allI, rule allI, rule allI, rule impI, rule ballI)
      fix k horst_strategy board square
      assume "valid_game horst_strategy ?queenie_strategy k board" "square \<in> squares"
      then show "(board square = Some Knight) = (board (cycle_opposite square) = Some Queen)"
      proof (induction horst_strategy ?queenie_strategy k board arbitrary: square rule: valid_game.induct)
        case (1 horst_strategy)
        then show ?case
          by (simp add: empty_board_def)
      next
        case (2 horst_strategy K board board' board'')
        show ?case
        proof safe
          assume "board'' square = Some Knight"
          show "board'' (cycle_opposite square) = Some Queen"
          proof (cases "board square = Some Knight")
            case True
            then have "board (cycle_opposite square) = Some Queen"
              using 2
              by blast
            then have "board' (cycle_opposite square) = Some Queen"
              using \<open>valid_horst_move board board'\<close>
              unfolding valid_horst_move_def valid_horst_move'_def
              by (metis fun_upd_apply option.distinct(1))
            then show ?thesis
              using \<open>valid_queenie_move board' board''\<close>
              using valid_queenie_move_def
              by auto
          next
            case False
            from \<open>valid_queenie_move board' board''\<close> \<open>?queenie_strategy board' board''\<close>
            obtain square' where 
              "square' \<in> squares"
              "board' square' = Some Knight"
              "board' (cycle_opposite square') = None"
              "board'' (cycle_opposite square') = Some Queen"
              by auto

            have "square = square'"
            proof (rule ccontr)
              assume "square \<noteq> square'"
              then have "board square' = Some Knight"
                using \<open>board'' square = Some Knight\<close> \<open>board' square' = Some Knight\<close> \<open>valid_horst_move board board'\<close> \<open>valid_queenie_move board' board''\<close> 
                by (smt False map_upd_Some_unfold piece.distinct(1) valid_horst_move'_def valid_horst_move_def valid_queenie_move_def)
              then have "board (cycle_opposite square') = Some Queen"
                using \<open>square' \<in> squares\<close> 2 
                by simp
              then have "board' (cycle_opposite square') = Some Queen"
                by (metis \<open>board' (cycle_opposite square') = None\<close> \<open>valid_horst_move board board'\<close> fun_upd_def valid_horst_move'_def valid_horst_move_def)
              then show False
                using \<open>board' (cycle_opposite square') = None\<close>
                by simp
            qed
            then show ?thesis
              using \<open>board'' (cycle_opposite square') = Some Queen\<close>
              by simp
          qed
        next
          assume "board'' (cycle_opposite square) = Some Queen"
          show "board'' square = Some Knight"
          proof (cases "board (cycle_opposite square) = Some Queen")
            case True
            then have "board square = Some Knight"
              using 2
              by auto
            then have "board' square = Some Knight"
              using \<open>valid_horst_move board board'\<close>
              unfolding valid_horst_move_def valid_horst_move'_def valid_queenie_move_def
              by auto
            then show ?thesis
              using \<open>valid_queenie_move board' board''\<close>
              unfolding valid_queenie_move_def
              by auto
          next
            case False
            then have "board' (cycle_opposite square) \<noteq> Some Queen"
              using \<open>valid_horst_move board board'\<close>
              unfolding valid_horst_move_def valid_horst_move'_def valid_queenie_move_def
              by (meson map_upd_Some_unfold piece.simps(2))
            obtain square' where "square' \<in> squares" 
              "board' (cycle_opposite square') = None" 
              "board'' (cycle_opposite square') = Some Queen"
              "board' square' = Some Knight"
              using \<open>?queenie_strategy board' board''\<close>
              by auto
            moreover
            obtain square'' where "board' square'' = None" 
              "board'' = board' (square'' := Some Queen)"
              using \<open>valid_queenie_move board' board''\<close>
              unfolding valid_queenie_move_def
              by auto
            ultimately
            have "cycle_opposite square' = square''"
              by (auto split: if_split_asm)
            then have "cycle_opposite square' = cycle_opposite square"
              using \<open>board'' (cycle_opposite square) = Some Queen\<close>
              using \<open>board' (cycle_opposite square) \<noteq> Some Queen\<close>
              using \<open>board'' = board' (square'' := Some Queen)\<close>
              by (auto split: if_split_asm)
            then have "cycle_opposite (cycle_opposite square') = cycle_opposite (cycle_opposite square)"
              by simp
            then have "square' = square"
              by simp
            then have "board' square = Some Knight"
              using \<open>board' square' = Some Knight\<close>
              by simp
            then show ?thesis
              using \<open>board'' = board'(square'' \<mapsto> Queen)\<close>
                    \<open>board' (cycle_opposite square') = None\<close>
                    \<open>cycle_opposite square' = square''\<close> \<open>square' = square\<close>
              by auto
          qed
        qed
      qed
    qed

    have "valid_queenie_strategy ?queenie_strategy"
      unfolding valid_queenie_strategy_def
    proof safe
      fix horst_strategy board board' k f r
      assume "valid_game horst_strategy ?queenie_strategy k board"
             "valid_horst_move board board'" "horst_strategy board board'"
      then obtain square where 
       *: "square \<in> squares" "board square = None" "\<not> attacks_knight square board" "board' = board(square \<mapsto> Knight)"
        unfolding valid_horst_move_def valid_horst_move'_def
        by auto
      have "board (cycle_opposite square) \<noteq> Some Queen" "board (cycle_opposite square) \<noteq> Some Knight"
        using 1[rule_format, OF \<open>valid_game horst_strategy ?queenie_strategy k board\<close>, of square]
        using 1[rule_format, OF \<open>valid_game horst_strategy ?queenie_strategy k board\<close>, of "cycle_opposite square"]
        using \<open>square \<in> squares\<close> \<open>board square = None\<close>
        by auto
      then have "board (cycle_opposite square) = None"
        by (metis (full_types) option.exhaust_sel piece.exhaust)

      let ?board = "board' (cycle_opposite square := Some Queen)"
      have "?queenie_strategy board' ?board"
        using * \<open>board (cycle_opposite square) = None\<close> \<open>square \<in> squares\<close>
        by (rule_tac x=square in bexI, simp_all)

      moreover

      obtain f' r' where "cycle_opposite square = (f', r')"
        by (cases "cycle_opposite square")
      then have "valid_queenie_move board' ?board"
        using  \<open>board (cycle_opposite square) = None\<close> cycle_opposite_squares[of square]
        unfolding valid_queenie_move_def
        by (metis "*"(1) "*"(4) cycle_opposite_different fun_upd_other)

      ultimately
      show "\<exists> board''.
              valid_queenie_move board' board'' \<and>
              ?queenie_strategy board' board''"
        by blast
    qed

    then obtain board where **: "valid_game horst_strategy ?queenie_strategy k board"
      using *
      by auto

    have "card (knights board) > (files * ranks) div 4"
      using valid_game_knights_card[rule_format, OF **] \<open>k > (files * ranks) div 4\<close>
      by auto

    have "card (cycle ` (knights board)) > (files * ranks) div 4"
    proof-
      have "inj_on cycle (knights board)"
        unfolding inj_on_def
      proof (rule ballI, rule ballI, rule impI)
        fix square1 square2
        assume "square1 \<in> knights board" "square2 \<in> knights board" "cycle square1 = cycle square2"
        then show "square1 = square2"
          using 1[rule_format, OF \<open>valid_game horst_strategy ?queenie_strategy k board\<close>]
          using valid_game_not_attacks_knight[rule_format, OF \<open>valid_game horst_strategy ?queenie_strategy k board\<close>]
          using cycle_exhausted[of board]
          unfolding knights_def
          by blast
      qed
      then show ?thesis
        using \<open>card (knights board) > (files * ranks) div 4\<close>
        by (simp add: card_image)
    qed

    moreover

    have "cycle ` (knights board) \<subseteq> cycle ` squares"
      unfolding knights_def
      by auto

    moreover

    have "finite (cycle ` squares)"
      by simp

    ultimately

    have "card (cycle ` squares) > (files * ranks) div 4"
      using card_mono
      by (smt zle_int)

    then show False
      using cycles_card
      by simp
  qed
qed

lemma guaranteed_game_lengths_finite: 
  shows "finite guaranteed_game_lengths"
proof (subst finite_nat_set_iff_bounded_le)
  show "\<exists>m. \<forall>n\<in>guaranteed_game_lengths. n \<le> m"
  proof (rule_tac x="nat ((files*ranks) div 4)" in exI)
    show "\<forall>n\<in>guaranteed_game_lengths. n \<le> nat (files * ranks div 4)"
      using guaranteed_game_lengths_leq pos
      by auto
  qed
qed

theorem IMO2018SL_C2:
  shows "Max guaranteed_game_lengths = nat ((files * ranks) div 4)"
proof (rule Max_eqI)
  show "nat ((files * ranks) div 4) \<in> guaranteed_game_lengths"
    using guaranteed_game_lengths_geq
    by auto
next
  fix k
  assume "k \<in> guaranteed_game_lengths"
  then show "k \<le> nat ((files * ranks) div 4)"
    using guaranteed_game_lengths_leq
    by auto 
next
  show "finite guaranteed_game_lengths"
    using guaranteed_game_lengths_finite
    by auto
qed

end

end