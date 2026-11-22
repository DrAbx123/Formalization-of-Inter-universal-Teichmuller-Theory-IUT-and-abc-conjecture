import tmp.sheaf.xif.paper.Mzk1Lemma22GChoiceConstructActual
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-! # Mzk1GChoiceDegreeActual — degree of the g-choice polynomial g = f(lambda X) + f0q

STEP 0 prior-art: corpus Lemma 2.2 lines 116-135 (f nonconstant); consumer construction
Mzk1Lemma22GChoiceConstructActual (gPoly/eval/collapse GREEN+CITABLE); Mathlib Polynomial
natDegree API (natDegree_comp, natDegree_C_mul_X, natDegree_mul, natDegree_pow,
natDegree_X_pow, natDegree_X_sub_C, natDegree_add_eq_left_of_natDegree_lt) reused.
This file proves g is nonconstant (natDegree >= m+n >= 2), completing the hdeg input of
Mzk1GChoiceData. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual

/-- lam = alpha2^-1 is nonzero (since scaled set has a positive point r = alpha1/alpha2). -/
theorem lam_ne_zero (D : Mzk1ScaleData) : D.lam ≠ 0 := by
  have hα2 : D.alpha2 ≠ 0 := by
    have hr0 := D.hr0
    intro h
    rw [D.r_eq, h, div_zero] at hr0
    norm_num at hr0
  rw [D.lam_eq]
  exact inv_ne_zero hα2

/-- The degree of the inner base polynomial x^m (x-1)^n is m + n. -/
theorem base_natDegree (D : Mzk1ScaleData) :
    ((X : ℚ[X]) ^ D.m * ((X : ℚ[X]) - 1) ^ D.n).natDegree = D.m + D.n := by
  have hXm_ne : ((X : ℚ[X]) ^ D.m) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hsub_ne : ((X : ℚ[X]) - 1) ^ D.n ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1)
  rw [Polynomial.natDegree_mul hXm_ne hsub_ne, Polynomial.natDegree_X_pow]
  have hsub : (((X : ℚ[X]) - 1) ^ D.n).natDegree = D.n := by
    rw [Polynomial.natDegree_pow]
    have h1 : ((X : ℚ[X]) - 1).natDegree = 1 := by
      simpa using Polynomial.natDegree_X_sub_C (1 : ℚ)
    rw [h1, Nat.mul_one]
  rw [hsub]

/-- The composed inner polynomial has degree m + n. -/
theorem comp_natDegree (D : Mzk1ScaleData) :
    ((((X : ℚ[X]) ^ D.m * ((X : ℚ[X]) - 1) ^ D.n).comp (C D.lam * X))).natDegree
      = D.m + D.n := by
  rw [Polynomial.natDegree_comp, base_natDegree D,
    Polynomial.natDegree_C_mul_X D.lam (lam_ne_zero D), Nat.mul_one]

/-- g is nonconstant: natDegree >= 2. -/
theorem gPoly_natDegree_pos (D : Mzk1ScaleData) : 1 ≤ (gPoly D).natDegree := by
  have hlt : (C (f0q D)).natDegree <
      ((((X : ℚ[X]) ^ D.m * ((X : ℚ[X]) - 1) ^ D.n).comp (C D.lam * X))).natDegree := by
    rw [Polynomial.natDegree_C, comp_natDegree D]
    have hm' : 1 ≤ D.m := D.hm
    have hn' : 1 ≤ D.n := D.hn
    omega
  have hg : (gPoly D).natDegree =
      ((((X : ℚ[X]) ^ D.m * ((X : ℚ[X]) - 1) ^ D.n).comp (C D.lam * X))).natDegree := by
    unfold gPoly
    exact Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt
  rw [hg, comp_natDegree D]
  have hm' : 1 ≤ D.m := D.hm
  have hn' : 1 ≤ D.n := D.hn
  omega

#check lam_ne_zero
#check base_natDegree
#check comp_natDegree
#check gPoly_natDegree_pos

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
end
