section\<open>Combinatorics problems\<close>

subsection \<open>IMO 2017 SL - C1\<close>

theory IMO_2017_SL_C1
  imports Complex_Main
begin

type_synonym square = "nat \<times> nat"

(*
fun green :: "square \<Rightarrow> bool" where
  "green (x, y) \<longleftrightarrow> (x + y) mod 2 = 0"

fun yellow :: "square \<Rightarrow> bool" where
  "yellow (x, y) \<longleftrightarrow> (x + y) mod 2 \<noteq> 0"
*)

text \<open>A rectangle with vertices [x1, x2) and [y1, y2) is given by a quadruple (x1, x2, y1, y2).\<close>
type_synonym rect = "nat \<times> nat \<times> nat \<times> nat"

fun valid_rect :: "rect \<Rightarrow> bool" where
  "valid_rect (x1, x2, y1, y2) \<longleftrightarrow> x1 < x2 \<and> y1 < y2"

text \<open>All squares in a rectangle\<close>
fun squares :: "rect \<Rightarrow> square set" where
  "squares (x1, x2, y1, y2) = {x1..<x2} \<times> {y1..<y2}"

(*
text \<open>One rectangle is inside another one\<close>
definition inside :: "rect \<Rightarrow> rect \<Rightarrow> bool" where
  "inside ri ro \<longleftrightarrow> squares ri \<subseteq> squares ro"
*)

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

(*
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
  sorry

lemma finite_green_squares [simp]:
  shows "finite (green_squares r)"
  using finite_subset[of "green_squares r" "squares r"]
  sorry

lemma finite_yellow_squares [simp]:
  shows "finite (yellow_squares r)"
  using finite_subset[of "yellow_squares r" "squares r"]
  sorry

lemma card_green_squares_row:
  assumes "x1 < x2"
  shows "card {(x, y). x1 \<le> x \<and> x < x2 \<and> y = y0 \<and> green (x, y)} = 
         (if yellow (x1, y0) then (x2 - x1) div 2 else (x2 - x1 + 1) div 2)"
  sorry

lemma card_squares:
  shows "card (squares (x1, x2, y1, y2)) = (x2 - x1) * (y2 - y1)"
  sorry

lemma card_green_squares_start_yellow:
  assumes "yellow (x1, y1)" "valid_rect (x1, x2, y1, y2)"
  shows "card (green_squares (x1, x2, y1, y2)) = (x2 - x1) * (y2 - y1) div 2"
  sorry

lemma card_yellow_squares_start_yellow:
  assumes "yellow (x1, y1)" "valid_rect (x1, x2, y1, y2)"
  shows "card (yellow_squares (x1, x2, y1, y2)) = ((x2 - x1) * (y2 - y1) + 1) div 2"
  sorry

lemma card_yellow_squares_start_green:
  assumes "green (x1, y1)" "valid_rect (x1, x2, y1, y2)"
  shows "card (yellow_squares (x1, x2, y1, y2)) = (x2 - x1) * (y2 - y1) div 2"
  sorry

lemma card_green_squares_start_green:
  assumes "green (x1, y1)" "valid_rect (x1, x2, y1, y2)"
  shows "card (green_squares (x1, x2, y1, y2)) = ((x2 - x1) * (y2 - y1) + 1) div 2"
  sorry

lemma mixed_rect: 
  assumes "valid_rect (x1, x2, y1, y2)" "mixed_rect (x1, x2, y1, y2)"
        shows "card (green_squares (x1, x2, y1, y2)) = card (yellow_squares (x1, x2, y1, y2))"
  sorry

lemma green_rect: 
  assumes "valid_rect (x1, x2, y1, y2)"  "green_rect (x1, x2, y1, y2)"
  shows "card (green_squares (x1, x2, y1, y2)) = card (yellow_squares (x1, x2, y1, y2)) + 1"
  sorry

lemma yellow_rect: 
  assumes "valid_rect (x1, x2, y1, y2)" "yellow_rect (x1, x2, y1, y2)"
  shows "card (green_squares (x1, x2, y1, y2)) + 1 = card (yellow_squares (x1, x2, y1, y2))"
  sorry

lemma tiles_inside:
  assumes "tiles rs (x1, x2, y1, y2)" "r \<in> rs"
  shows "inside r (x1, x2, y1, y2)"
  sorry

lemma finite_tiles:
  assumes "tiles rs (x1, x2, y1, y2)" "\<forall> r \<in> rs. valid_rect r"
  shows "finite rs"
  sorry

lemma green_tile:
  assumes "green_rect (0, a, 0, b)" "a > 0" "b > 0"
          "tiles rs (0, a, 0, b)" "\<forall> r \<in> rs. valid_rect r"
  shows "\<exists> r \<in> rs. green_rect r"
  sorry
*)

theorem IMO_2017_SL_C1:
  fixes a b :: nat                                          
  assumes "odd a" "odd b" "tiles rs (0, a, 0, b)" "\<forall> r \<in> rs. valid_rect r"
        shows "\<exists> (x1, x2, y1, y2) \<in> rs. 
                  let ds = {x1 - 0, a - x2, y1 - 0, b - y2} 
                   in (\<forall> d \<in> ds. even d) \<or> (\<forall> d \<in> ds. odd d)"
  sorry

end