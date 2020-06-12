subsection \<open>IMO 2006 SL - A4\<close>

theory IMO_2006_SL_A4
imports Complex_Main
begin

theorem IMO_2006_SL_A4:
  fixes a :: "nat \<Rightarrow> real" and n :: nat
  assumes 
    "\<forall> i. 1 \<le> i \<and> i \<le> n \<longrightarrow> a i > 0"
  shows 
    "(\<Sum> i = 1..<n. \<Sum> j = i+1..n. (a i * a j / (a i + a j))) \<le> 
     (n / (2 * (\<Sum> i = 1..n. a i)) * (\<Sum> i = 1..<n. \<Sum> j = i+1..n. (a i * a j)))"
  sorry


end