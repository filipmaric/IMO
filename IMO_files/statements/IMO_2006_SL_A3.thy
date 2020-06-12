subsection \<open>IMO 2006 SL - A3\<close>

theory IMO_2006_SL_A3
  imports Complex_Main

begin

theorem IMO_2006_SL_A3:
  fixes c :: "nat \<Rightarrow> nat" 
   and  S :: "(nat \<times> nat) set"
  assumes "c 0 = 1" "c 1 = 0" "\<forall> n \<ge> 0. c (n + 2) = c (n + 1) + c n" and
    "\<forall> (x, y) \<in> S. \<exists> J :: nat set. (\<forall> j \<in> J. j > 0) \<and> 
    x = (\<Sum>j\<in>J. c j) \<and> y = (\<Sum>j\<in>J. c (j-1))"
  shows "\<exists> \<alpha> \<beta> m M :: real. (x,y) \<in> S \<longleftrightarrow> (m < \<alpha> * x + \<beta> * y \<and> \<alpha> * x + \<beta> * y  < M)"
  sorry

end