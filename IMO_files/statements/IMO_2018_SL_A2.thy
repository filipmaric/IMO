subsection \<open>IMO 2018 SL - A2\<close>

theory IMO_2018_SL_A2
imports Complex_Main
begin

theorem IMO2018SL_A2:
  fixes n :: nat
  assumes "n \<ge> 3"
  shows "(\<exists> a :: nat \<Rightarrow> real. a n = a 0 \<and> a (n+1) = a 1 \<and> 
                             (\<forall> i < n. (a i) * (a (i+1)) + 1 = a (i+2))) \<longleftrightarrow> 
         3 dvd n" (is "(\<exists> a. ?p1 a \<and> ?p2 a \<and> ?eq a) \<longleftrightarrow> 3 dvd n")
  sorry

end