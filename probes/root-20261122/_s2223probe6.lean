
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section
open WeierstrassCurve

namespace S2223Probe

variable {F : Type*} [Field F] [CharZero F]
variable (W : WeierstrassCurve F) [W.IsElliptic]

example (L : Type*) [Field L] [CharZero L] [Algebra F L] (x : L) :
    let y : L := -((W.baseChange L).a₁ * x + (W.baseChange L).a₃) / 2
    (W.baseChange L).twoTorsionPolynomial.toPoly.eval x = 0 → (W.baseChange L).toAffine.Equation x y := by
  intro y hx
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

end S2223Probe
end
