subsection \<open>IMO 2006 SL - A6\<close>

theory IMO_2006_SL_A6
  imports Complex_Main
begin

theorem IMO_2006_SL_A6:
  fixes a b c :: real
  shows "Min {M. \<forall> a b c. \<bar>a * b * (a\<^sup>2 - b\<^sup>2) + b * c * (b\<^sup>2 - c\<^sup>2) + c * a * (c\<^sup>2 - a\<^sup>2)\<bar> \<le> M * (a\<^sup>2 + b\<^sup>2 + c\<^sup>2)\<^sup>2} = (sqrt 2) * 9 / 32"
  sorry

end
