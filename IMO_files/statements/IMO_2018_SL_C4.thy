subsection \<open>IMO 2018 SL - C4\<close>

theory IMO_2018_SL_C4
  imports Main "HOL-Library.Permutation"
begin

definition antipascal :: "(nat \<Rightarrow> nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> bool" where
   "antipascal f n \<longleftrightarrow> (\<forall> r < n. \<forall> c \<le> r. f r c = abs (f (r+1) c - f (r+1) (c+1)))"

definition triangle :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
  "triangle r0 c0 n = {(r, c) | r c :: nat. r0 \<le> r \<and> r < r0 + n \<and> c0 \<le> c \<and> c \<le> c0 + r - r0}"
(*
lemma triangle_finite [simp]:
  shows "finite (triangle r0 c0 n)"
  sorry

lemma triangle_card:
  shows "card (triangle r0 c0 n) = n * (n+1) div 2"
  sorry
*)
fun uncurry where
   "uncurry f (a, b) = f a b"
(*
lemma gauss: 
  fixes n :: nat
  shows "sum_list [1..<n] = n * (n - 1) div 2"
  sorry

lemma sum_list_insort [simp]:
  fixes x :: nat and xs :: "nat list"
  shows "sum_list (insort x xs) = x + sum_list xs"
  sorry

lemma sum_list_sort [simp]:
  fixes xs :: "nat list"
  shows "sum_list (sort xs) = sum_list xs"
  sorry

lemma sorted_distinct_strict_increase:
  assumes "sorted (xs @ [x])" "distinct (xs @ [x])" "\<forall> x \<in> set (xs @ [x]). x > a"
  shows "x > a + length xs"
  sorry

lemma sum_list_sorted_distinct_lb:
  assumes "\<forall> x \<in> set xs. x > a" "distinct xs" "sorted xs"
  shows "sum_list xs \<ge> length xs * (2 * a + length xs + 1) div 2"
  sorry

lemma sum_list_distinct_lb:
  assumes "\<forall> x \<in> set xs. f x > a" "distinct (map f xs)"
  shows "(\<Sum> x \<leftarrow> xs. f x) \<ge> length xs * (2 * a + length xs + 1) div 2"
  sorry

lemma consecutive_nats_sorted:
  assumes "sorted xs" "length xs = n" "distinct xs" "sum_list xs \<le> n * (n + 1) div 2" "\<forall> x \<in> set xs. x > 0"
  shows "xs = [1..<n+1]"
  sorry

lemma consecutive_nats:
  assumes "length xs = n" "distinct xs" "sum_list xs \<le> n * (n + 1) div 2" "\<forall> x \<in> set xs. x > 0"
  shows "set xs = {1..<n+1}"
  sorry

lemma sum_list_cong:
  assumes "\<forall> x \<in> set xs. f x = g x"
  shows "(\<Sum> x \<leftarrow> xs. f x) = (\<Sum> x \<leftarrow> xs. g x)"
  sorry

lemma sum_list_last:
  assumes "a \<le> b"
  shows "(\<Sum> x \<leftarrow> [a..<b+1]. f x) = (\<Sum> x \<leftarrow> [a..<b]. f x) + f b"
  sorry

lemma sum_list_nat:
  assumes "\<forall> x \<in> set xs. f x \<ge> 0"
  shows "(\<Sum> x \<leftarrow> xs. nat (f x)) = (nat (\<Sum> x \<leftarrow> xs. f x))"
  using assms
  sorry
*)
theorem IMO2018SL_C4:
  "\<nexists> f. antipascal f 2018 \<and> 
   (uncurry f) ` triangle 0 0 2018  = {1..<2018*(2018 + 1) div 2 + 1}"
  sorry

end