/- R3a (1/n): actual division polynomials for the Legendre family.

  RECON: `LeanFormal.IUT.legendreWeierstrassCurve` (equation y² = x(x-1)(x-parameter),
  LegendreWeierstrassCurve.lean:27) with b₂/b₄/b₆/b₈ simp lemmas; Mathlib
  `WeierstrassCurve.Ψ₃ = 3X⁴ + C b₂·X³ + 3·C b₄·X² + 3·C b₆·X + C b₈`
  (DivisionPolynomial/Basic.lean:142). 2-torsion coordinates from
  `Mzk1ULLegendreTwoTorsionActual` (x = 0,1,λ); 3/5/l coordinates are built from Ψ₃, Ψ₅, Ψ_l here
  and in `Mzk1G1F2ThetaTorsionCoords`/`ThetaTorsionFive`.
  Mathlib has no `n • P = 0 ↔ ψₙ(x) = 0` for n ≥ 3 (see EllipticDivisionPolynomialEvaluation
  header); n=3 comes from `S1373ZeroCriterionActual`, n=5/l need the multiplication-kernel route.
  No sorry/axiom. -/
import LeanFormal.IUT.ABCBridge.Geometry.LegendreWeierstrassCurve
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaDivisionPolynomialsActual
open LeanFormal.IUT

variable {R : Type*} [CommRing R]

/-- The `3`-division polynomial of the Legendre family, written in the exact shape of Mathlib's
    `Ψ₃` (Basic.lean:142) with the Legendre coefficients substituted. -/
noncomputable def legendreΨ₃ (parameter : R) : Polynomial R :=
  3 * X ^ 4 + C (-4 * (1 + parameter)) * X ^ 3 + 3 * C (2 * parameter) * X ^ 2 +
    3 * C (0 : R) * X + C (-(parameter ^ 2))

/-- `legendreΨ₃` is Mathlib's `Ψ₃` of the Legendre curve. -/
theorem legendre_Ψ₃_eq (parameter : R) :
    (legendreWeierstrassCurve parameter).Ψ₃ = legendreΨ₃ parameter := by
  simp only [WeierstrassCurve.Ψ₃, legendreWeierstrassCurve_b₂,
    legendreWeierstrassCurve_b₄, legendreWeierstrassCurve_b₆,
    legendreWeierstrassCurve_b₈, legendreΨ₃]

/-- Evaluation form of `legendreΨ₃`. -/
theorem legendreΨ₃_eval (parameter x : R) :
    (legendreΨ₃ parameter).eval x =
      3 * x ^ 4 - 4 * (1 + parameter) * x ^ 3 + 6 * parameter * x ^ 2 - parameter ^ 2 := by
  simp [legendreΨ₃]
  ring

#print axioms legendre_Ψ₃_eq
#print axioms legendreΨ₃_eval

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaDivisionPolynomialsActual