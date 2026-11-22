/- R3a (3/n): Ψ₅ and Ψ_l for the Legendre family (odd division polynomials), and their root sets.

  RECON: Mathlib `WeierstrassCurve.preΨ n` (DivisionPolynomial/Basic.lean) and the odd-n
  univariate reduction `Ψ_eq_C_preΨ_of_odd` (EllipticDivisionPolynomialEvaluation.lean:113).
  `Ψ 5`/`Ψ l` have no group-law bridge in the tree (S1373 header; route §5.2 says use the actual
  multiplication-kernel description): here we realize the kernel as the root set of `preΨ n`,
  i.e. the ACTUAL division-polynomial roots (not a splitting field). No sorry/axiom. -/
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import LeanFormal.IUT.ABCBridge.Geometry.LegendreWeierstrassCurve
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTorsionFiveActual
open LeanFormal.IUT

variable {R : Type*} [CommRing R]

/-- Legendre `Ψ_n` for odd `n`, realized as Mathlib's `preΨ n` (univariate in the x-coordinate). -/
noncomputable def legendreΨn (parameter : R) (n : ℤ) : Polynomial R :=
  (legendreWeierstrassCurve parameter).preΨ n

/-- `legendreΨn` is Mathlib's `Ψ_n` for odd `n`. -/
theorem legendre_Ψn_eq (parameter : R) {n : ℤ} (hn : ¬ Even n) :
    (legendreWeierstrassCurve parameter).Ψ n = C (legendreΨn parameter n) := by
  rw [WeierstrassCurve.Ψ_eq_C_preΨ_of_odd (W := legendreWeierstrassCurve parameter) hn]
  rfl

/-- Legendre `Ψ₅`. -/
noncomputable def legendreΨ₅ (parameter : R) : Polynomial R := legendreΨn parameter 5

/-- Legendre `Ψ₅` is Mathlib's `Ψ 5`. -/
theorem legendre_Ψ₅_eq (parameter : R) :
    (legendreWeierstrassCurve parameter).Ψ 5 = C (legendreΨ₅ parameter) := by
  exact legendre_Ψn_eq parameter (by decide : ¬ Even (5 : ℤ))

/-- `ψ_n` on the Legendre curve only sees `x` and equals `legendreΨn` at the x-coordinate. -/
theorem evalDivisionPolynomial_legendre_odd {x y : R}
    (h : (legendreWeierstrassCurve parameter).toAffine.Equation x y) {n : ℤ} (hn : ¬ Even n) :
    (legendreWeierstrassCurve parameter).evalDivisionPolynomial x y n =
      (legendreΨn parameter n).eval x := by
  rw [WeierstrassCurve.evalDivisionPolynomial_eq_eval_preΨ_of_odd
    (W := legendreWeierstrassCurve parameter) h hn]
  rfl

/-- **E[5] 的 x-坐标集**（`legendreΨ₅` 的根，实际 multiplication kernel）。 -/
noncomputable def fiveTorsionX (parameter : ℂ) : Set ℂ :=
  {x : ℂ | (legendreΨ₅ parameter).eval x = 0}

#print axioms legendre_Ψn_eq
#print axioms legendre_Ψ₅_eq
#print axioms evalDivisionPolynomial_legendre_odd

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTorsionFiveActual