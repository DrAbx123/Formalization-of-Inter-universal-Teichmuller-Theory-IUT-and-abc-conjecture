import tmp.sheaf.xif.paper.Mzk1G1JHeightBezoutActual
import tmp.sheaf.xif.paper.Mzk1G1QHeightActual
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1JHeightLowerActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1QHeightActual
open LeanFormal.IUT.XiFPaper.G1JHeightBezoutActual
open MvPolynomial

variable {K : Type*} [Field K] [NumberField K]

/-! ### Homogeneity of the integer Bezout coefficients -/

private lemma isHomogeneous_four_mul (a b : ℕ) (c : MvPolynomial (Fin 2) ℤ)
    (hc : c.IsHomogeneous 0) (hab : a + b = 4) :
    (c * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)
      : MvPolynomial (Fin 2) ℤ).IsHomogeneous 4 := by
  have h1 : (MvPolynomial.X 0 ^ a : MvPolynomial (Fin 2) ℤ).IsHomogeneous a :=
    MvPolynomial.isHomogeneous_X_pow (σ := Fin 2) (R := ℤ) 0 a
  have h2 : (MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) ℤ).IsHomogeneous b :=
    MvPolynomial.isHomogeneous_X_pow (σ := Fin 2) (R := ℤ) 1 b
  have h3 := hc.mul (h1.mul h2)
  simpa [hab] using h3

private lemma isHomogeneous_numeral_zero (n : ℕ) :
    ((n : MvPolynomial (Fin 2) ℤ)).IsHomogeneous 0 := by
  have h : (n : MvPolynomial (Fin 2) ℤ) = MvPolynomial.C (n : ℤ) := by
    rw [← MvPolynomial.algebraMap_eq]
    exact (map_natCast (algebraMap ℤ (MvPolynomial (Fin 2) ℤ)) n).symm
  rw [h]
  exact MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := ℤ) (n : ℤ)

set_option maxHeartbeats 800000 in
theorem jQ00Z_isHomogeneous : (jQ00Z).IsHomogeneous 4 := by
  unfold jQ00Z
  have t1 := isHomogeneous_four_mul 2 2 (-(3 : MvPolynomial (Fin 2) ℤ))
    (isHomogeneous_numeral_zero 3).neg (by norm_num)
  have t2 := isHomogeneous_four_mul 3 1 (3 : MvPolynomial (Fin 2) ℤ)
    (isHomogeneous_numeral_zero 3) (by norm_num)
  have t3 := isHomogeneous_four_mul 4 0 (1 : MvPolynomial (Fin 2) ℤ)
    (isHomogeneous_numeral_zero 1) (by norm_num)
  simpa [pow_one, pow_zero, add_assoc] using (t1.add t2).add t3

set_option maxHeartbeats 800000 in
theorem jQ01Z_isHomogeneous : (jQ01Z).IsHomogeneous 4 := by
  unfold jQ01Z
  have t1 := isHomogeneous_four_mul 0 4 (3 : MvPolynomial (Fin 2) ℤ)
    (isHomogeneous_numeral_zero 3) (by norm_num)
  have t2 := isHomogeneous_four_mul 1 3 (-(6 : MvPolynomial (Fin 2) ℤ))
    (isHomogeneous_numeral_zero 6).neg (by norm_num)
  have t3 := isHomogeneous_four_mul 2 2 (11 : MvPolynomial (Fin 2) ℤ)
    (isHomogeneous_numeral_zero 11) (by norm_num)
  have t4 := isHomogeneous_four_mul 3 1 (-(8 : MvPolynomial (Fin 2) ℤ))
    (isHomogeneous_numeral_zero 8).neg (by norm_num)
  have t5 := isHomogeneous_four_mul 4 0 (6 : MvPolynomial (Fin 2) ℤ)
    (isHomogeneous_numeral_zero 6) (by norm_num)
  have hsum : ((3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
      + (-(6 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
      + (11 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
      + (-(8 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1)
      + (6 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0)).IsHomogeneous 4 :=
    (by simpa [pow_one, pow_zero, add_assoc] using ((t1.add t2).add (t3.add t4)).add t5)
  simpa [pow_one, pow_zero, add_assoc] using (isHomogeneous_numeral_zero 256).mul hsum

set_option maxHeartbeats 800000 in
theorem jQ10Z_isHomogeneous : (jQ10Z).IsHomogeneous 4 := by
  unfold jQ10Z
  have t1 := isHomogeneous_four_mul 0 4 (1 : MvPolynomial (Fin 2) ℤ)
    (isHomogeneous_numeral_zero 1) (by norm_num)
  have t2 := isHomogeneous_four_mul 1 3 (3 : MvPolynomial (Fin 2) ℤ)
    (isHomogeneous_numeral_zero 3) (by norm_num)
  have t3 := isHomogeneous_four_mul 2 2 (-(3 : MvPolynomial (Fin 2) ℤ))
    (isHomogeneous_numeral_zero 3).neg (by norm_num)
  simpa [pow_one, pow_zero, add_assoc] using (t1.add t2).add t3

set_option maxHeartbeats 800000 in
theorem jQ11Z_isHomogeneous : (jQ11Z).IsHomogeneous 4 := by
  unfold jQ11Z
  have t1 := isHomogeneous_four_mul 0 4 (6 : MvPolynomial (Fin 2) ℤ)
    (isHomogeneous_numeral_zero 6) (by norm_num)
  have t2 := isHomogeneous_four_mul 1 3 (-(8 : MvPolynomial (Fin 2) ℤ))
    (isHomogeneous_numeral_zero 8).neg (by norm_num)
  have t3 := isHomogeneous_four_mul 2 2 (11 : MvPolynomial (Fin 2) ℤ)
    (isHomogeneous_numeral_zero 11) (by norm_num)
  have t4 := isHomogeneous_four_mul 3 1 (-(6 : MvPolynomial (Fin 2) ℤ))
    (isHomogeneous_numeral_zero 6).neg (by norm_num)
  have t5 := isHomogeneous_four_mul 4 0 (3 : MvPolynomial (Fin 2) ℤ)
    (isHomogeneous_numeral_zero 3) (by norm_num)
  have hsum : ((6 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
      + (-(8 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
      + (11 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
      + (-(6 : MvPolynomial (Fin 2) ℤ)) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1)
      + (3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0)).IsHomogeneous 4 :=
    (by simpa [pow_one, pow_zero, add_assoc] using ((t1.add t2).add (t3.add t4)).add t5)
  simpa [pow_one, pow_zero, add_assoc] using (isHomogeneous_numeral_zero 256).mul hsum

#print axioms jQ00Z_isHomogeneous
#print axioms jQ01Z_isHomogeneous
#print axioms jQ10Z_isHomogeneous
#print axioms jQ11Z_isHomogeneous

end LeanFormal.IUT.XiFPaper.G1JHeightLowerActual
end
