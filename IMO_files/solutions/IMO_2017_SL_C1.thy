theory IMO_2017_SL_C1
  imports Complex_Main
begin

type_synonym square = "nat \<times> nat"

fun green :: "square \<Rightarrow> bool" where
  "green (x, y) \<longleftrightarrow> (x + y) mod 2 = 0"

fun yellow :: "square \<Rightarrow> bool" where
  "yellow (x, y) \<longleftrightarrow> (x + y) mod 2 \<noteq> 0"

text \<open>A rectangle [x1, x2) \<times> [y1, y2) is given by a quadruple (x1, x2, y1, y2).\<close>
type_synonym rect = "nat \<times> nat \<times> nat \<times> nat"

fun valid_rect :: "rect \<Rightarrow> bool" where
  "valid_rect (x1, x2, y1, y2) \<longleftrightarrow> x1 < x2 \<and> y1 < y2"

text \<open>All squares in a rectangle\<close>
fun squares :: "rect \<Rightarrow> square set" where
  "squares (x1, x2, y1, y2) = {x1..<x2} \<times> {y1..<y2}"

text \<open>One rectangle is inside another one\<close>
definition inside :: "rect \<Rightarrow> rect \<Rightarrow> bool" where
  "inside ri ro \<longleftrightarrow> squares ri \<subseteq> squares ro"

text \<open>Two rectangles overlap inside another one\<close>
definition overlap :: "rect \<Rightarrow> rect \<Rightarrow> bool" where
  "overlap r1 r2 \<longleftrightarrow> squares r1 \<inter> squares r2 \<noteq> {}"

text \<open>There are no two overlapping rectangles in a set\<close>
definition non_overlapping :: "rect set \<Rightarrow> bool" where
  "non_overlapping rs \<longleftrightarrow> (\<forall> r1 \<in> rs. \<forall> r2 \<in> rs. r1 \<noteq> r2 \<longrightarrow> \<not> overlap r1 r2)"

text \<open>A set of rectangles covers a given rectangle\<close>
definition cover :: "rect set \<Rightarrow> rect \<Rightarrow> bool" where
  "cover rs r \<longleftrightarrow> (\<Union> (squares ` rs)) = squares r"

text \<open>A rectangle is tiled by a set of non-overlapping, smaller rectangles\<close>
definition tiles :: "rect set \<Rightarrow> rect \<Rightarrow> bool" where
  "tiles rs r \<longleftrightarrow> cover rs r \<and> non_overlapping rs"

text \<open>All green squares in a rectangle\<close>
definition green_squares where
  "green_squares r = {(x, y) \<in> squares r. green (x, y)}"

text \<open>All yellow squares in a rectangle\<close>
definition yellow_squares where
  "yellow_squares r = {(x, y) \<in> squares r. yellow (x, y)}"

text \<open>Corner squares of a rectangle\<close>
fun corners :: "rect \<Rightarrow> (nat \<times> nat) set" where
  "corners (x1, x2, y1, y2) = {(x1, y1), (x1, y2-1), (x2-1, y1), (x2-1, y2-1)}"

definition green_rect :: "rect \<Rightarrow> bool" where
  "green_rect r \<longleftrightarrow> (\<forall> c \<in> corners r. green c)"

definition yellow_rect :: "rect \<Rightarrow> bool" where
  "yellow_rect r \<longleftrightarrow> (\<forall> c \<in> corners r. yellow c)"

definition mixed_rect ::  "rect \<Rightarrow> bool" where
  "mixed_rect r \<longleftrightarrow> \<not> green_rect r \<and> \<not> yellow_rect r"

lemma finite_squares [simp]:
  shows "finite (squares r)"
  by (cases r, auto)

lemma finite_green_squares [simp]:
  shows "finite (green_squares r)"
  using finite_subset[of "green_squares r" "squares r"]
  by (auto simp add: green_squares_def)

lemma finite_yellow_squares [simp]:
  shows "finite (yellow_squares r)"
  using finite_subset[of "yellow_squares r" "squares r"]
  by (auto simp add: yellow_squares_def)

lemma card_green_squares_row:
  assumes "x1 < x2"
  shows "card {(x, y). x1 \<le> x \<and> x < x2 \<and> y = y0 \<and> green (x, y)} = 
         (if yellow (x1, y0) then (x2 - x1) div 2 else (x2 - x1 + 1) div 2)"
  using assms
proof (induction k \<equiv> "x2 - x1 - 1" arbitrary: x2)
  case 0
  hence "x2 = x1 + 1"
    by simp
  hence "{(x, y). x1 \<le> x \<and> x < x2 \<and> y = y0 \<and> green (x, y)} =
         {(x, y). x = x1 \<and> y = y0 \<and> green (x, y)}"
    by auto
  also have "... = (if yellow (x1, y0) then {} else {(x1, y0)})"
    by auto
  finally show ?case
    using `x2 = x1 + 1`
    by (smt One_nat_def Suc_1 Suc_eq_plus1 add_diff_cancel_left' card_empty card_insert_if div_self equals0D finite.intros(1) nat.simps(3) one_div_two_eq_zero)
next
  case (Suc k)
  let ?S = "{(x, y). x1 \<le> x \<and> x < x2 \<and> y = y0 \<and> green (x, y)}"
  let ?S1 = "{(x, y). x1 \<le> x \<and> x < x2 - 1 \<and> y = y0 \<and> green (x, y)}"
  let ?S2 = "{(x, y). x = x2 - 1 \<and> y = y0 \<and> green (x, y)}"
  have "card (?S1 \<union> ?S2) = card ?S1 + card ?S2"
  proof (rule card_Un_disjoint)
    show "finite ?S1"
      using finite_subset[of ?S1 "{x1..<x2} \<times> {y0}"]
      by force
  next
    show "finite ?S2"
      using finite_subset[of ?S2 "{x2-1} \<times> {y0}"]
      by auto
  next
    show "?S1 \<inter> ?S2 = {}"
      by auto
  qed
  moreover
  have "?S = ?S1 \<union> ?S2"
    using `x1 < x2`
    by auto
  ultimately
  have 1: "card ?S = card ?S1 + card ?S2"
    by simp
  have 2: "card ?S1 = (if yellow (x1, y0) then (x2 - 1 - x1) div 2 else (x2 - x1) div 2)"
    using Suc(1)[of "x2 - 1"] Suc(2) Suc(3)
    by auto
  show ?case
  proof (cases "yellow (x1, y0)")
    case True
    show ?thesis
    proof (cases "green (x2-1, y0)")
      case True
      hence "even (x2 - x1)"
        using `x1 < x2` `yellow (x1, y0)`
        by simp presburger
      hence "(x2 - x1) div 2 = (x2 - x1 - 1) div 2 + 1"
        using `x1 < x2`
        by presburger+
      moreover
      have "?S2 = {(x2-1, y0)}"
        using `green (x2-1, y0)`
        by auto
      then have "card ?S2 = 1"
        by simp
      ultimately show ?thesis
        using `yellow (x1, y0)` 1 2 True
        by simp
    next
      case False
      hence "odd (x2 - x1)"
        using `yellow (x1, y0)` `x1 < x2`
        by simp presburger
      hence "(x2 - x1) div 2 = (x2 - x1 - 1) div 2"
        using `x2 > x1`
        by presburger
      moreover
      have "?S2 = {}"
        using False
        by auto
      then have "card ?S2 = 0"
        by (metis card_empty)
      ultimately show ?thesis
        using `yellow (x1, y0)` 1 2
        by simp
    qed
  next
    case False
    hence "green (x1, y0)"
      by simp
    show ?thesis
    proof (cases "green (x2-1, y0)")
      case True
      hence "odd (x2 - x1)"
        using `green (x1, y0)` `x1 < x2`
        by simp presburger
      hence "(x2 - x1) div 2 + 1 = (x2 - x1 + 1) div 2"
        using `x1 < x2`
        by presburger
      moreover
      have "?S2 = {(x2-1, y0)}"
        using True
        by auto
      then have "card ?S2 = 1"
        by simp
      ultimately show ?thesis
        using 1 2 `green (x1, y0)`
        by simp
    next
      case False
      hence "even (x2 - x1)"
        using `green (x1, y0)` `x1 < x2`
        by simp presburger
      hence "(x2 - x1) div 2 = (x2 - x1 + 1) div 2"
        using `x2 > x1`
        by presburger
      moreover
      have "?S2 = {}"
        using False
        by auto
      then have "card ?S2 = 0"
        by (metis card_empty)
      ultimately show ?thesis
        using 1 2 `green (x1, y0)`
        by simp
    qed
  qed
qed

lemma card_squares:
  shows "card (squares (x1, x2, y1, y2)) = (x2 - x1) * (y2 - y1)"
  by simp

lemma card_green_squares_start_yellow:
  assumes "yellow (x1, y1)" "valid_rect (x1, x2, y1, y2)"
  shows "card (green_squares (x1, x2, y1, y2)) = (x2 - x1) * (y2 - y1) div 2"
  using assms
proof (induction k \<equiv> "y2 - y1 - 1" arbitrary: y2)
  case 0
  hence "y2 = y1 + 1"
    by simp
  thus ?case
    using `yellow (x1, y1)` `valid_rect (x1, x2, y1, y2)` card_green_squares_row[of x1 x2 y1]
    unfolding green_squares_def
    by simp
next
  case (Suc k)

  have "x1 < x2" "y1 < y2" 
    using `valid_rect (x1, x2, y1, y2)`
    by simp_all

  let ?S = "green_squares (x1, x2, y1, y2)"
  let ?S1 = "green_squares (x1, x2, y1, y2-1)"
  let ?S2 = "{(x, y). x1 \<le> x \<and> x < x2 \<and> y = y2-1 \<and> green (x, y)}"

  have 1: "card ?S1 = (x2 - x1) * (y2 - 1 - y1) div 2"
    using Suc
    by auto

  have "card (?S1 \<union> ?S2) = card ?S1 + card ?S2"
  proof (rule card_Un_disjoint)
    show "finite ?S1"
      using finite_subset[of ?S1 "{x1..<x2} \<times> {y1..<y2}"]
      unfolding green_squares_def
      by force
  next
    show "finite ?S2"
      using finite_subset[of ?S2 "{x1..<x2} \<times> {y2 - 1}"]
      by force
  next
    show "?S1 \<inter> ?S2 = {}"
      unfolding green_squares_def
      by auto
  qed

  moreover

  have "?S = ?S1 \<union> ?S2"
    using `y1 < y2`
    by (auto simp add: green_squares_def)

  ultimately

  have 2: "card ?S = card ?S1 + card ?S2"
    by simp

  show ?case
  proof (cases "odd (y2 - y1)")
    case True
    hence "yellow (x1, y2-1)"
      using `y1 < y2` `yellow (x1, y1)`
      by simp presburger
    hence "card ?S2 = (x2 - x1) div 2"
      using card_green_squares_row[of x1 x2 "y2-1"] `x1 < x2`
      by simp
    hence "card ?S = (x2 - x1) * (y2 - y1 - 1) div 2 + (x2 - x1) div 2"
      using 1 2
      by simp
    also have "... = (x2 - x1) * (y2 - y1) div 2"
      using `odd (y2 - y1)` `x1 < x2` `y1 < y2`
      by (metis add_mult_distrib2 div_plus_div_distrib_dvd_left dvdI dvd_mult nat_mult_1_right odd_two_times_div_two_nat odd_two_times_div_two_succ)
    finally show ?thesis
      .
  next
    case False
    hence "green (x1, y2-1)"
      using `y1 < y2` `yellow (x1, y1)`
      by simp presburger
    hence "card ?S2 = (x2 - x1 + 1) div 2"
      using card_green_squares_row[of x1 x2 "y2-1"] `x1 < x2`
      by simp
    hence "card ?S = (x2 - x1) * (y2 - y1 - 1) div 2 + (x2 - x1 + 1) div 2"
      using 1 2
      by simp
    also have "... = (x2 - x1) * (y2 - y1) div 2"
      using `\<not> odd (y2 - y1)` `x1 < x2` `y1 < y2`
      apply (cases "odd (x2 - x1)")
       apply (smt Suc_diff_Suc add.commute add_Suc_shift diff_diff_left div_mult_self2 even_add even_mult_iff mult_Suc_right odd_two_times_div_two_succ plus_1_eq_Suc zero_neq_numeral)
      apply (metis Suc_diff_1 add.commute dvd_div_mult even_succ_div_two mult_Suc_right zero_less_diff)
      done
    finally show ?thesis
      .
  qed
qed

lemma card_yellow_squares_start_yellow:
  assumes "yellow (x1, y1)" "valid_rect (x1, x2, y1, y2)"
  shows "card (yellow_squares (x1, x2, y1, y2)) = ((x2 - x1) * (y2 - y1) + 1) div 2"
proof-
  let ?S = "squares (x1, x2, y1, y2)" and ?Y = "yellow_squares (x1, x2, y1, y2)" and ?G = "green_squares (x1, x2, y1, y2)"
  have "?S = ?Y \<union> ?G"
    unfolding green_squares_def yellow_squares_def
    by auto
  moreover
  have "card (?Y \<union> ?G) = card ?Y + card ?G"
  proof (rule card_Un_disjoint)
    show "finite ?Y"
      using finite_subset[of ?Y ?S]
      by (force simp add: yellow_squares_def)
  next
    show "finite ?G"
      using finite_subset[of ?G ?S]
      by (force simp add: green_squares_def)
  next
    show "?Y \<inter> ?G = {}"
      by (auto simp add: yellow_squares_def green_squares_def)
  qed
  ultimately
  have "card ?S = card ?G + card ?Y"
    by simp
  hence "card ?Y = card ?S - card ?G"
    by auto
  hence "card ?Y = (x2 - x1)*(y2 - y1) - (x2 - x1)*(y2 - y1) div 2"
    using assms(1) assms(2) card_green_squares_start_yellow card_squares
    by presburger
  also have "... = ((x2 - x1)*(y2 - y1) + 1) div 2"
    by presburger
  finally show ?thesis
    .
qed

lemma card_yellow_squares_start_green:
  assumes "green (x1, y1)" "valid_rect (x1, x2, y1, y2)"
  shows "card (yellow_squares (x1, x2, y1, y2)) = (x2 - x1) * (y2 - y1) div 2"
proof-
  let ?Y = "yellow_squares (x1, x2, y1, y2)" and ?G = "green_squares (x1+1, x2+1, y1, y2)"
  have "card ?Y = card ?G"
  proof (rule bij_betw_same_card)
    let ?f = "\<lambda> (x, y). (x+1, y)"
    show "bij_betw ?f ?Y ?G"
      unfolding bij_betw_def
    proof safe
      show "inj_on ?f ?Y"
        by (auto simp add: inj_on_def)
    next
      fix x y
      assume "(x, y) \<in> ?Y"
      then show "(x+1, y) \<in> ?G"
        unfolding green_squares_def yellow_squares_def
        by (auto simp add: mod_Suc)
    next
      fix x y
      assume "(x, y) \<in> ?G"
      hence "(x-1, y) \<in> ?Y" "x > 0"
        unfolding green_squares_def yellow_squares_def
        apply auto
        apply (metis Nat.add_diff_assoc2 Suc_eq_plus1 add_eq_if add_leD2 even_Suc even_iff_mod_2_eq_zero not_mod2_eq_Suc_0_eq_0 odd_add)
        by (metis Suc_leI add_gr_0 even_iff_mod_2_eq_zero lessI mod_nat_eqI not_mod2_eq_Suc_0_eq_0 numeral_2_eq_2 odd_even_add odd_pos)
      thus "(x, y) \<in> ?f ` ?Y"
        by (simp add: rev_image_eqI)
    qed
  qed
  thus ?thesis
    using card_green_squares_start_yellow[of "x1+1" y1 "x2+1" y2] `valid_rect (x1, x2, y1, y2)`
    using `green (x1, y1)`
    by auto
qed

lemma card_green_squares_start_green:
  assumes "green (x1, y1)" "valid_rect (x1, x2, y1, y2)"
  shows "card (green_squares (x1, x2, y1, y2)) = ((x2 - x1) * (y2 - y1) + 1) div 2"
proof-
  let ?G = "green_squares (x1, x2, y1, y2)" and ?Y = "yellow_squares (x1+1, x2+1, y1, y2)"
  have "card ?G = card ?Y"
  proof (rule bij_betw_same_card)
    let ?f = "\<lambda> (x, y). (x+1, y)"
    show "bij_betw ?f ?G ?Y"
      unfolding bij_betw_def
    proof safe
      show "inj_on ?f ?G"
        by (auto simp add: inj_on_def)
    next
      fix x y
      assume "(x, y) \<in> ?G"
      then show "(x+1, y) \<in> ?Y"
        unfolding green_squares_def yellow_squares_def
        by auto
    next
      fix x y
      assume "(x, y) \<in> ?Y"
      hence "(x-1, y) \<in> ?G" "x > 0"
        unfolding green_squares_def yellow_squares_def
        apply auto
        apply (metis Suc_eq_plus1 add_eq_if even_Suc even_iff_mod_2_eq_zero not_mod2_eq_Suc_0_eq_0 odd_add)
        done
      thus "(x, y) \<in> ?f ` ?G"
        by (simp add: rev_image_eqI)
    qed
  qed
  thus ?thesis
    using card_yellow_squares_start_yellow[of "x1+1" y1 "x2+1" y2] `valid_rect (x1, x2, y1, y2)`
    using `green (x1, y1)`
    by auto
qed

lemma mixed_rect: 
  assumes "valid_rect (x1, x2, y1, y2)" "mixed_rect (x1, x2, y1, y2)"
        shows "card (green_squares (x1, x2, y1, y2)) = card (yellow_squares (x1, x2, y1, y2))"
proof (cases "green (x1, y1)")
  case True
  then have "even ((x2 - x1) * (y2 - y1))"
    using assms
    unfolding mixed_rect_def green_rect_def yellow_rect_def
    by auto presburger+
  thus ?thesis
    using True
    using card_green_squares_start_green[of x1 y1 x2 y2] assms
    using card_yellow_squares_start_green[of x1 y1 x2 y2]
    by simp
next
  case False
  then have "even ((x2 - x1) * (y2 - y1))"
    using assms
    unfolding mixed_rect_def green_rect_def yellow_rect_def
    by auto presburger+
  thus ?thesis
    using False
    using card_green_squares_start_yellow[of x1 y1 x2 y2] assms
    using card_yellow_squares_start_yellow[of x1 y1 x2 y2]
    unfolding mixed_rect_def green_rect_def yellow_rect_def
    by simp
qed

lemma green_rect: 
  assumes "valid_rect (x1, x2, y1, y2)"  "green_rect (x1, x2, y1, y2)"
  shows "card (green_squares (x1, x2, y1, y2)) = card (yellow_squares (x1, x2, y1, y2)) + 1"
  using assms
  using card_green_squares_start_green[of x1 y1 x2 y2]
  using card_yellow_squares_start_green[of x1 y1 x2 y2]
  unfolding green_rect_def
  by auto
  
lemma yellow_rect: 
  assumes "valid_rect (x1, x2, y1, y2)" "yellow_rect (x1, x2, y1, y2)"
  shows "card (green_squares (x1, x2, y1, y2)) + 1 = card (yellow_squares (x1, x2, y1, y2))"
  using assms
  using card_green_squares_start_yellow[of x1 y1 x2 y2]
  using card_yellow_squares_start_yellow[of x1 y1 x2 y2]
  unfolding yellow_rect_def
  by auto (metis dvd_imp_mod_0 even_Suc even_diff_nat even_mult_iff linorder_not_less nat_less_le odd_Suc_div_two odd_add)

lemma tiles_inside:
  assumes "tiles rs (x1, x2, y1, y2)" "r \<in> rs"
  shows "inside r (x1, x2, y1, y2)"
  using assms
  unfolding tiles_def inside_def cover_def
  by auto

lemma finite_tiles:
  assumes "tiles rs (x1, x2, y1, y2)" "\<forall> r \<in> rs. valid_rect r"
  shows "finite rs"
proof (rule finite_subset)
  show "rs \<subseteq> {0..x2} \<times> {0..x2} \<times> {0..y2} \<times> {0..y2}"
  proof
    fix r :: rect
    obtain x1r x2r y1r y2r where r: "r = (x1r, x2r, y1r, y2r)"
      by (cases r)
    assume "r \<in> rs"
    then have "inside r (x1, x2, y1, y2)"
      using tiles_inside[OF assms(1)]
      by auto
    moreover have "x1r < x2r" "y1r < y2r"
      using assms(2) `r \<in> rs` r
      by auto
    ultimately
    show "r \<in> {0..x2} \<times> {0..x2} \<times> {0..y2} \<times> {0..y2}"
      using r times_subset_iff[of "{x1r..<x2r}" "{y1r..<y2r}" "{x1..<x2}" "{y1..<y2}"]
      by (auto simp add: inside_def)
  qed
next
  show "finite ({0..x2} \<times> {0..x2} \<times> {0..y2} \<times> {0..y2})"
    by simp
qed


lemma green_tile:
  assumes "green_rect (0, a, 0, b)" "a > 0" "b > 0"
          "tiles rs (0, a, 0, b)" "\<forall> r \<in> rs. valid_rect r"
  shows "\<exists> r \<in> rs. green_rect r"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence *: "\<forall> r \<in> rs. yellow_rect r \<or> mixed_rect r"
    using mixed_rect_def by blast

  have **: "\<forall> r \<in> rs. card (green_squares r) \<le> card (yellow_squares r)"
  proof
    fix r
    assume "r \<in> rs"
    obtain x1 x2 y1 y2 where r: "r = (x1, x2, y1, y2)"
      by (cases r, auto)


    have "yellow_rect r \<or> mixed_rect r"
      using `r \<in> rs` *
      by simp
    thus "card (green_squares r) \<le> card (yellow_squares r)"
    proof
      assume "yellow_rect r"
      thus ?thesis
        using yellow_rect[of x1 x2 y1 y2] r assms(5) `r \<in> rs`
        by auto
    next
      assume "mixed_rect r"
      thus ?thesis
        using mixed_rect[of x1 x2 y1 y2] r assms(5) `r \<in> rs`
        by auto
    qed
  qed

  have "card (green_squares (0, a, 0, b)) \<le> card (yellow_squares (0, a, 0, b))"
  proof-
    have "card (green_squares (0, a, 0, b)) = card (\<Union> (green_squares ` rs))"
    proof-
      have "green_squares (0, a, 0, b) = \<Union> (green_squares ` rs)"
        using `tiles rs (0, a, 0, b)`
        unfolding tiles_def cover_def green_squares_def
        by blast
      thus ?thesis
        by simp
    qed
    also have "... = (\<Sum> r \<in> rs. card (green_squares r))"
    proof (rule card_UN_disjoint)
      show "finite rs"
        using assms(4) assms(5) finite_tiles by auto
    next
      show "\<forall> r \<in> rs. finite (green_squares r)"
        by auto
    next
      show "\<forall> r1 \<in> rs. \<forall> r2 \<in> rs. r1 \<noteq> r2 \<longrightarrow> green_squares r1 \<inter> green_squares r2 = {}"
      proof (rule, rule, rule)
        fix r1 r2
        assume "r1 \<in> rs" "r2 \<in> rs" "r1 \<noteq> r2"
        then have "squares r1 \<inter> squares r2 = {}"
          using `tiles rs (0, a, 0, b)`
          unfolding tiles_def non_overlapping_def overlap_def
          by auto
        then show "green_squares r1 \<inter> green_squares r2 = {}"
          unfolding green_squares_def
          by auto
      qed
    qed
    also have "... \<le> (\<Sum> r \<in> rs. card (yellow_squares r))"
      using **
      by (simp add: sum_mono)
    also have "... = card (\<Union> (yellow_squares ` rs))"
    proof (rule card_UN_disjoint[symmetric])
      show "finite rs"
        using assms(4) assms(5) finite_tiles by auto
    next
      show "\<forall>r\<in>rs. finite (yellow_squares r)"
        by auto
    next
      show "\<forall>r\<in>rs. \<forall>j\<in>rs. r \<noteq> j \<longrightarrow> yellow_squares r \<inter> yellow_squares j = {}"
      proof (rule, rule, rule)
        fix r1 r2
        assume "r1 \<in> rs" "r2 \<in> rs" "r1 \<noteq> r2"
        then have "squares r1 \<inter> squares r2 = {}"
          using `tiles rs (0, a, 0, b)`
          unfolding tiles_def non_overlapping_def overlap_def
          by auto
        then show "yellow_squares r1 \<inter> yellow_squares r2 = {}"
          unfolding yellow_squares_def
          by auto
      qed
    qed
    also have "... = card (yellow_squares (0, a, 0, b))"
    proof-
      have "yellow_squares (0, a, 0, b) = \<Union> (yellow_squares ` rs)"
        using `tiles rs (0, a, 0, b)`
        unfolding tiles_def cover_def yellow_squares_def
        by blast
      thus ?thesis
        by simp
    qed

    finally
    show ?thesis
      .
  qed

  thus False
    using `green_rect (0, a, 0, b)` green_rect[of 0 a 0 b] `a > 0` `b > 0`
    by auto
qed

theorem IMO_2017_SL_C1:
  fixes a b :: nat                                          
  assumes "odd a" "odd b" "tiles rs (0, a, 0, b)" "\<forall> r \<in> rs. valid_rect r"
        shows "\<exists> (x1, x2, y1, y2) \<in> rs. 
                  let ds = {x1 - 0, a - x2, y1 - 0, b - y2} 
                   in (\<forall> d \<in> ds. even d) \<or> (\<forall> d \<in> ds. odd d)"
proof-
  have "green_rect (0, a, 0, b)"
    using \<open>odd a\<close> \<open>odd b\<close>
    unfolding green_rect_def
    by auto
  then obtain x1 x2 y1 y2 where 
     *: "green_rect (x1, x2, y1, y2)" "(x1, x2, y1, y2) \<in> rs"
    using green_tile[of a b rs] assms
    by (auto simp add: odd_pos)

  have **: "x1 < x2" "x2 \<le> a" "y1 < y2" "y2 \<le> b"
    using tiles_inside[of rs 0 a 0 b "(x1, x2, y1, y2)"] assms(4) *(2) assms(3)
      times_subset_iff[of "{x1..<x2}" "{y1..<y2}" "{0..<a}" "{0..<b}"]
    by (auto simp add: inside_def)

  show ?thesis
  proof (rule_tac x="(x1, x2, y1, y2)" in bexI)
    show "(x1, x2, y1, y2) \<in> rs"
      by fact
  next
    show "case (x1, x2, y1, y2) of
              (x1, x2, y1, y2) \<Rightarrow> let ds = {x1 - 0, a - x2, y1 - 0, b - y2} in (\<forall>d\<in>ds. even d) \<or> (\<forall>d\<in>ds. odd d)"
      using `odd a` `odd b` ** `green_rect (x1, x2, y1, y2)`
      by (auto simp add: Let_def green_rect_def)
  qed
qed


end