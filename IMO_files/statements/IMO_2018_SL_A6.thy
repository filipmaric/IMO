subsection \<open>IMO 2018 SL - A6\<close>

theory IMO_2018_SL_A6
  imports Main Complex_Main 
  HOL.Rat
  "HOL-Algebra.Polynomials"
begin

lemma IMO_2018_SL_A6:
  fixes n m :: nat
  assumes 
    "n \<ge> 2" and "m \<ge> 2" and 
    "\<forall> (S :: nat set). card S = n \<and> 
    (\<forall> x \<in> S. x \<in> {0..<m}) \<and> 
    polynomial S f \<and>
    f (list S) = floor (Frakt (\<Sum> x \<in> S) m)"
  shows "degree f \<ge> n" 
  sorry

end