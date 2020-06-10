subsection \<open>IMO 2018 SL - A7\<close>

theory IMO_2018_SL_A7
imports Complex_Main
begin

theorem
  shows "Max {root 3 (a / (b + 7)) + root 3 (b / (c + 7)) + root 3 (c / (d + 7)) + root 3 (d / (a + 7)) 
              | a b c d :: real . a \<ge> 0 \<and> b \<ge> 0 \<and> c \<ge> 0 \<and> d \<ge> 0 \<and> a + b + c + d = 100} = 8 / root 3 7"
  sorry

end
