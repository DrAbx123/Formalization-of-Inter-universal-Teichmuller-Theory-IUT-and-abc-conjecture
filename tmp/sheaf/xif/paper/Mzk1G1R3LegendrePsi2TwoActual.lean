/- R3 minimal instance (Lead 01:xx): `ψ₂(2P)·ψ₂(P)³ = preΨ₄(P)` for `a₁ = a₃ = a₆ = 0`
(Legendre normal form: `a₂ = -(1+λ)`, `a₄ = λ`). REUSE: `psi2AtTwo`/`psi2AtTwo_eq`,
`two_nsmul_slope_eq`/`two_nsmul_addY_eq` (this lane); Mathlib `preΨ₄`, `b₂..b₈`.
Denominator hypotheses: `y ≠ 0` and `(2 : F) ≠ 0`. -/
import tmp.sheaf.xif.paper.Mzk1G1R3TwoNsmulPsy2Actual
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

noncomputable section
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R3LegendrePsi2TwoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulXActual
open LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulYActual
open LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulPsy2Actual

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- Under `a₁ = a₃ = 0`, `ψ₂(2P) = 2·Y₂`. -/
theorem psi2AtTwo_eq_two_mul_addY (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) (x y : F) :
    psi2AtTwo W x y = 2 * W.addY x x y (W.slope x x y y) := by
  unfold psi2AtTwo
  rw [h1, h3]
  ring

/-- `y ≠ 0` implies `y ≠ negY x y` when `a₁ = a₃ = 0` and `(2 : F) ≠ 0`. -/
theorem ne_negY_of_a1a3 (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) (h2 : (2 : F) ≠ 0)
    {x y : F} (hy : y ≠ 0) : y ≠ W.negY x y := by
  intro h
  rw [WeierstrassCurve.Affine.negY, h1, h3] at h
  simp only [zero_mul, sub_zero, add_zero] at h
  apply hy
  have h2y : (2 : F) * y = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2y).resolve_left h2

/-- **Closed form of `ψ₂(2P)·(2y)³`** for `a₁ = a₃ = 0`: `-2N³ + 8y²N(a₂+3x) - 16y⁴`,
where `N = 3x² + 2a₂x + a₄`. -/
theorem psi2AtTwo_mul_cube_closed (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) (h2 : (2 : F) ≠ 0)
    {x y : F} (hy : y ≠ 0) :
    psi2AtTwo W x y * (2 * y) ^ 3 =
      -2 * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 3
        + 8 * y ^ 2 * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) * (W.a₂ + 3 * x)
        - 16 * y ^ 4 := by
  have hy' : y ≠ W.negY x y := ne_negY_of_a1a3 W h1 h3 h2 hy
  have h2y : (2 : F) * y ≠ 0 := mul_ne_zero h2 hy
  have hslope : W.slope x x y y = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) / (2 * y) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy', WeierstrassCurve.Affine.negY, h1, h3]
    congr 1 <;> ring
  rw [psi2AtTwo_eq_two_mul_addY W h1 h3, two_nsmul_addY_eq W hy', hslope]
  simp only [WeierstrassCurve.Affine.addX, h1, h3, zero_mul, zero_add, add_zero, sub_zero,
    mul_zero]
  field_simp [hy, h2, h2y]
  ring_nf

/-- **Minimal instance of the M2 identity** (`a₁ = a₃ = a₆ = 0`, `(2:F) ≠ 0`):
`ψ₂(2P)·ψ₂(P)³ = preΨ₄(P)`, where `ψ₂(P) = 2y`. -/
theorem psi2AtTwo_mul_cube (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) (h6 : W.a₆ = 0)
    (h2 : (2 : F) ≠ 0) {x y : F}
    (hEq : y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x) (hy : y ≠ 0) :
    psi2AtTwo W x y * (2 * y) ^ 3 = (W.preΨ 4).eval x := by
  have hy4 : y ^ 4 = (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x) ^ 2 := by
    rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, hEq]
  rw [psi2AtTwo_mul_cube_closed W h1 h3 h2 hy, hy4, hEq, WeierstrassCurve.preΨ_four,
    show W.preΨ₄ = 2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4
      + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2
      + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2) from rfl]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, h1, h3, h6, zero_mul, zero_add, add_zero, sub_zero, mul_zero]
  simp
  ring_nf

#print axioms psi2AtTwo_eq_two_mul_addY
#print axioms psi2AtTwo_mul_cube_closed
#print axioms psi2AtTwo_mul_cube
end LeanFormal.IUT.XiFPaper.Mzk1G1R3LegendrePsi2TwoActual
