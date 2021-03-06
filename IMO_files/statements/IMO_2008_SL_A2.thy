subsection \<open>IMO 2008 SL - A2\<close>

theory IMO_2008_SL_A2
imports Complex_Main
begin

theorem IMO_2008_SL_A2_a:
  fixes x y z :: real
  assumes "x \<noteq> 1" "y \<noteq> 1" "z \<noteq> 1" "x * y * z = 1"
  shows "x\<^sup>2 / (x - 1)\<^sup>2 + y\<^sup>2 / (y - 1)\<^sup>2 + z\<^sup>2 / (z - 1)\<^sup>2 \<ge> 1"
  sorry

theorem IMO_2008_SL_A2_b:
  fixes x y z :: real
  shows "\<not> finite {(x, y, z). x \<noteq> 1 \<and> y \<noteq> 1 \<and> z \<noteq> 1 \<and> x * y * z = 1 \<and> x^2 / (x - 1)^2 + y^2 / (y - 1)^2 + z^2 / (z - 1)^2 = 1}"
  sorry

end