subsection \<open>IMO 2006 SL - A6\<close>

theory IMO_2006_SL_A6
  imports Complex_Main "HOL-ex.Sqrt"
begin

theorem IMO_2006_SL_A6:
  fixes a b c :: real
  shows "Max {(a * b * (a * a - b * b) + b * c * (b * b - c * c) + c * a * (c * c - a * a)) / (a * a + b * b + c * c)} = (sqrt 2) * 9 / 32"
  sorry

end
