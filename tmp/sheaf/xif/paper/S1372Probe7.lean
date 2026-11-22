import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
open Polynomial
open WeierstrassCurve
namespace Probe
variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)
lemma phi_eval {x y : K} (h : W.Nonsingular x y) (m : ℤ) :
    (W.Φ m).eval x =
      x * (W.evalDivisionPolynomial x y m) ^ 2 -
        W.evalDivisionPolynomial x y (m + 1) * W.evalDivisionPolynomial x y (m - 1) := by
  have hphi := WeierstrassCurve.evalEval_φ_eq_eval_Φ W h.1 m
  rw [show x * (W.evalDivisionPolynomial x y m) ^ 2 -
        W.evalDivisionPolynomial x y (m + 1) * W.evalDivisionPolynomial x y (m - 1)
      = Polynomial.evalEval x y (W.φ m) by
    simp [WeierstrassCurve.φ, WeierstrassCurve.evalDivisionPolynomial, Polynomial.evalEval, mul_comm]]
  exact hphi.symm
end Probe
