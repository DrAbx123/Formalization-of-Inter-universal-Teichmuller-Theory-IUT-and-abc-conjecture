import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual

open Polynomial
open LeanFormal.IUT
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

/-- Evaluation of the univariate `Φ_m` at a point in terms of `ψ`. -/
lemma phi_eval {x y : K} (h : W.Nonsingular x y) (m : ℤ) :
    (W.Φ m).eval x =
      x * (W.evalDivisionPolynomial x y m) ^ 2 -
        W.evalDivisionPolynomial x y (m + 1) * W.evalDivisionPolynomial x y (m - 1) := by
  have hphi := WeierstrassCurve.evalEval_φ_eq_eval_Φ W h.1 m
  rw [show x * (W.evalDivisionPolynomial x y m) ^ 2 -
        W.evalDivisionPolynomial x y (m + 1) * W.evalDivisionPolynomial x y (m - 1)
      = Polynomial.evalEval x y (W.φ m) by
    simp [WeierstrassCurve.φ, WeierstrassCurve.evalDivisionPolynomial, Polynomial.evalEval,
      mul_comm]]
  exact hphi.symm

/-- The recurrence for the x-coordinate of `(n+1) • P`, written with the
value of `ψ₂` at `n • P`. -/
lemma xCoord_recurrence {x y u v : K} (hP : W.Nonsingular x y) (hQ : W.Nonsingular u v)
    (hx : u ≠ x) :
    xCoord W (WeierstrassCurve.Affine.Point.some x y hP +
        WeierstrassCurve.Affine.Point.some u v hQ) =
      some (W.addX x u (W.slope x u y v)) ∧
    xCoord W (WeierstrassCurve.Affine.Point.some x y hP -
        WeierstrassCurve.Affine.Point.some u v hQ) =
      some (W.addX x u (W.slope x u y (W.negY u v))) ∧
    W.addX x u (W.slope x u y v) =
      W.addX x u (W.slope x u y (W.negY u v)) -
        (2 * y + W.a₁ * x + W.a₃) * (2 * v + W.a₁ * u + W.a₃) / (u - x) ^ 2 := by
  constructor
  · rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx, xCoord_some]
  constructor
  · have hne : x ≠ u := hx.symm
    have hsub : WeierstrassCurve.Affine.Point.some x y hP -
        WeierstrassCurve.Affine.Point.some u v hQ =
        WeierstrassCurve.Affine.Point.some x y hP +
          (-WeierstrassCurve.Affine.Point.some u v hQ) := by rw [sub_eq_add_neg]
    rw [hsub, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.add_of_X_ne hne, xCoord_some]
    congr 1
    rw [WeierstrassCurve.Affine.negY]
  · exact WeierstrassCurve.Affine.addX_eq_addX_negY_sub y v hx

end LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
