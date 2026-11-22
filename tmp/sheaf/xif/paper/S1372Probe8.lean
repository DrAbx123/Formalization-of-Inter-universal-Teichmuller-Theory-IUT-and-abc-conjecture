import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
open Polynomial
open WeierstrassCurve
namespace Probe2
variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)
noncomputable def xCoord : W.Point → Option K
  | .zero => none
  | .some x _ _ => some x
@[simp] lemma xCoord_some {x y : K} (h : W.Nonsingular x y) : xCoord W (WeierstrassCurve.Affine.Point.some x y h) = some x := rfl
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
  · rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx.symm, xCoord_some]
  constructor
  · have hne : x ≠ u := hx.symm
    have hsub : WeierstrassCurve.Affine.Point.some x y hP -
        WeierstrassCurve.Affine.Point.some u v hQ =
        WeierstrassCurve.Affine.Point.some x y hP +
          (-WeierstrassCurve.Affine.Point.some u v hQ) := by rw [sub_eq_add_neg]
    rw [hsub, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.add_of_X_ne hne, xCoord_some]
  · rw [WeierstrassCurve.Affine.addX_eq_addX_negY_sub y v hx.symm]
    have h1 : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
      rw [WeierstrassCurve.Affine.negY]; ring
    have h2 : v - W.negY u v = 2 * v + W.a₁ * u + W.a₃ := by
      rw [WeierstrassCurve.Affine.negY]; ring
    rw [h1, h2]
end Probe2