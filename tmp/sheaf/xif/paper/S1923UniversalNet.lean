import tmp.sheaf.xif.paper.S1923UniversalC2
import tmp.sheaf.xif.paper.S1923NetD2
import tmp.sheaf.xif.paper.S1377OmegaFormulaActual

set_option maxHeartbeats 1000000

noncomputable section
open Polynomial
open scoped Polynomial.Bivariate
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual

namespace WeierstrassCurve
namespace Universal

open Coeff

abbrev xU : Universal.Field := polyToField (Polynomial.C (Polynomial.X : Polynomial (MvPolynomial Coeff ℤ)))
abbrev yU : Universal.Field := polyToField (Polynomial.X : Poly)

lemma nonsingular_point : pointedCurve.toAffine.Nonsingular xU yU :=
  Affine.equation_iff_nonsingular.mp equation_point

lemma evalDivisionPolynomial_point (n : ℤ) :
    pointedCurve.evalDivisionPolynomial xU yU n = polyToField (curve.ψ n) := by
  change evalEval xU yU ((curve.map (algebraMap (MvPolynomial Coeff ℤ) Universal.Field)).ψ n) = _
  rw [map_ψ, evalEval_polyToField]

lemma evalDivisionPolynomial_point_two_ne_zero :
    pointedCurve.evalDivisionPolynomial xU yU 2 ≠ 0 := by
  rw [evalDivisionPolynomial_point]
  exact polyToField_ψ_ne_zero (by norm_num)

lemma evalDivisionPolynomial_point_ne_zero {k : ℤ} (hk : k ≠ 0) :
    pointedCurve.evalDivisionPolynomial xU yU k ≠ 0 := by
  rw [evalDivisionPolynomial_point]
  exact polyToField_ψ_ne_zero hk

lemma eval_even (m : ℤ) :
    pointedCurve.evalDivisionPolynomial xU yU (2 * m) * pointedCurve.evalDivisionPolynomial xU yU 2 =
      pointedCurve.evalDivisionPolynomial xU yU (m - 1) ^ 2 *
          pointedCurve.evalDivisionPolynomial xU yU m *
            pointedCurve.evalDivisionPolynomial xU yU (m + 2) -
        pointedCurve.evalDivisionPolynomial xU yU (m - 2) *
          pointedCurve.evalDivisionPolynomial xU yU m *
            pointedCurve.evalDivisionPolynomial xU yU (m + 1) ^ 2 := by
  have h := congrArg (Polynomial.evalEval xU yU) (pointedCurve.ψ_even m)
  simpa [WeierstrassCurve.evalDivisionPolynomial] using h

lemma eval_odd (m : ℤ) :
    pointedCurve.evalDivisionPolynomial xU yU (2 * m + 1) =
      pointedCurve.evalDivisionPolynomial xU yU (m + 2) *
          pointedCurve.evalDivisionPolynomial xU yU m ^ 3 -
        pointedCurve.evalDivisionPolynomial xU yU (m - 1) *
          pointedCurve.evalDivisionPolynomial xU yU (m + 1) ^ 3 := by
  have h := congrArg (Polynomial.evalEval xU yU) (pointedCurve.ψ_odd m)
  simpa [WeierstrassCurve.evalDivisionPolynomial] using h

lemma rel_even_point (m : ℤ) :
    IsEllipticNet.rel (fun n => pointedCurve.evalDivisionPolynomial xU yU n) (m + 1) (m - 1) 1 0 = 0 := by
  rw [IsEllipticNet.rel_even]
  have h := eval_even m
  simp only [WeierstrassCurve.evalDivisionPolynomial_one, one_pow, mul_one]
  linear_combination h

lemma rel_odd_point (m : ℤ) :
    IsEllipticNet.rel (fun n => pointedCurve.evalDivisionPolynomial xU yU n) (m + 1) m 1 0 = 0 := by
  rw [IsEllipticNet.rel_odd]
  have h := eval_odd m
  simp only [WeierstrassCurve.evalDivisionPolynomial_one, one_pow, mul_one]
  linear_combination h

lemma isEllipticNet_point :
    IsEllipticNet (fun n => pointedCurve.evalDivisionPolynomial xU yU n) := by
  apply S1923Net.IsEllipticNet.of_even_odd
  · intro n
    simp [WeierstrassCurve.evalDivisionPolynomial_neg]
  · simp
  · exact mem_nonZeroDivisors_of_ne_zero evalDivisionPolynomial_point_two_ne_zero
  · exact rel_even_point
  · exact rel_odd_point

end Universal
end WeierstrassCurve
