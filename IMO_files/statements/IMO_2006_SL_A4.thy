subsection \<open>IMO 2006 SL - A4\<close>

theory IMO_2006_SL_A4
imports Complex_Main
begin

theorem IMO_2006_SL_A4:
  fixes a :: "nat \<Rightarrow> real" and n :: nat
  assumes 
    "\<forall> i. 1 \<le> i \<and> i \<le> n \<and> a i > 0"
    "\<forall> n \<ge> 1. (\<Sum> k < Suc n. a (n - k) / (k + 1)) = 0" "n \<ge> 1"
  shows 
    "(\<Sum> i \<leftarrow> [1..<n]. \<Sum> j \<leftarrow> [i+1..<n+1]. (a i * a j / (a i + a j))) \<le> 
     (n / (2 * (\<Sum> i \<leftarrow> [1..<n+1]. a i)) * (\<Sum> i \<leftarrow> [1..<n]. \<Sum> j \<leftarrow> [i+1..<n+1]. (a i * a j)))"
  sorry

end