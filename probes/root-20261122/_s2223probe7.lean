
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation

noncomputable section
open WeierstrassCurve

namespace S2223Probe

variable {F : Type*} [Field F] [CharZero F]
variable (W : WeierstrassCurve F) [W.IsElliptic]

theorem twoTorsionPoint_of_root
    (L : Type*) [Field L] [CharZero L] [Algebra F L] [DecidableEq L] (x : L)
    (hx : (W.baseChange L).twoTorsionPolynomial.toPoly.eval x = 0) :
    ∃ (y : L) (h : (W.baseChange L).toAffine.Nonsingular x y),
      (2 : Nat) • (WeierstrassCurve.Affine.Point.some x y h) = 0 := by
  let y : L := -((W.baseChange L).a₁ * x + (W.baseChange L).a₃) / 2
  have heq : (W.baseChange L).toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    rw [WeierstrassCurve.twoTorsionPolynomial] at hx
    simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X] at hx
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hx
    change y ^ 2 + (W.baseChange L).a₁ * x * y + (W.baseChange L).a₃ * y =
      x ^ 3 + (W.baseChange L).a₂ * x ^ 2 + (W.baseChange L).a₄ * x + (W.baseChange L).a₆
    subst y
    field_simp
    ring_nf at hx
    ring_nf
    linear_combination (-1 : L) * hx
  have hΔ : (W.baseChange L).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    exact (map_ne_zero (algebraMap F L)).mpr (W.isUnit_Δ.ne_zero)
  have hns : (W.baseChange L).toAffine.Nonsingular x y :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero (W := (W.baseChange L)) hΔ).mp heq
  refine ⟨y, hns, ?_⟩
  have hdiv : (W.baseChange L).evalDivisionPolynomial x y 2 = 0 := by
    rw [WeierstrassCurve.evalDivisionPolynomial_two]
    change 2 * y + (W.baseChange L).a₁ * x + (W.baseChange L).a₃ = 0
    subst y
    field_simp
    ring
  have hy : y = (W.baseChange L).toAffine.negY x y :=
    (WeierstrassCurve.evalDivisionPolynomial_two_eq_zero_iff_negY (W := (W.baseChange L))).mp hdiv
  rw [show (2 : Nat) • (WeierstrassCurve.Affine.Point.some x y hns) =
      WeierstrassCurve.Affine.Point.some x y hns + WeierstrassCurve.Affine.Point.some x y hns by
    rw [two_nsmul]]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy

end S2223Probe
end
