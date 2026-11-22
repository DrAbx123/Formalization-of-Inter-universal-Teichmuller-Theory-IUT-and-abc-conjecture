import tmp.sheaf.xif.paper.S1923UniversalNet
import tmp.sheaf.xif.paper.S1377OmegaFormulaActual

set_option maxHeartbeats 1000000

noncomputable section
open Polynomial
open scoped Polynomial.Bivariate
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual

namespace WeierstrassCurve
namespace Universal

open Coeff

lemma eval_Φ_point (n : ℤ) :
    (pointedCurve.Φ n).eval xU = polyToField (Polynomial.C (curve.Φ n)) := by
  change ((curve.map (algebraMap (MvPolynomial Coeff ℤ) Universal.Field)).Φ n).eval xU = _
  rw [map_Φ, Polynomial.eval_map]
  change eval₂ (algebraMap (MvPolynomial Coeff ℤ) Universal.Field)
    (polyToField (Polynomial.C (Polynomial.X : Polynomial (MvPolynomial Coeff ℤ)))) (curve.Φ n) =
      polyToField (Polynomial.C (curve.Φ n))
  rw [x_eq]
  exact Polynomial.eval₂_algebraMap_X (curve.Φ n)
    (IsScalarTower.toAlgHom (MvPolynomial Coeff ℤ) (Polynomial (MvPolynomial Coeff ℤ)) Universal.Field)

lemma xCoordinateFormula_universal (n : ℤ) (hn : 1 ≤ n) :
    xCoord pointedCurve (n • WeierstrassCurve.Affine.Point.some xU yU nonsingular_point) =
      some (polyToField (Polynomial.C (curve.Φ n)) / (polyToField (curve.ψ n)) ^ 2) := by
  have hψ : ∀ k : ℤ, 1 ≤ k → k ≤ n + 1 →
      pointedCurve.evalDivisionPolynomial xU yU k ≠ 0 := by
    intro k hk1 hk2
    exact evalDivisionPolynomial_point_ne_zero (by omega)
  have h := (xCoordinate_and_omega_of_ellipticNet pointedCurve nonsingular_point
    isEllipticNet_point n hn hψ).1
  rw [h, eval_Φ_point, evalDivisionPolynomial_point]

end Universal
end WeierstrassCurve
