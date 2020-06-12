subsection \<open>IMO 2006 SL - A5\<close>

theory IMO_2006_SL_A5
  imports Complex_Main 
begin

theorem IMO_2006_SL_A5:
  fixes a b c :: nat
  assumes "a > 0" "b > 0" "c > 0" "a + b > c" "b + c > a" "c + a > b"
  shows "sqrt (b + c - a) / (sqrt b + sqrt c - sqrt a) + 
         sqrt (c + a - b) / (sqrt c + sqrt a - sqrt b) +
         sqrt (a + b - c) / (sqrt a + sqrt b - sqrt c) \<le> 3"
  sorry

end
