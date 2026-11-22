/- R3 general-W M2 identity (validated by the Legendre instance, DONE 19:30:36):
`ψ₂(2P)·(2y+a₁x+a₃)³ = preΨ₄(x)` on a general Weierstrass curve. REUSE:
`Mzk1G1R3TwoNsmulPsy2Actual.psi2AtTwo`/`psi2AtTwo_eq`, `Mzk1G1R3TwoNsmulYActual.two_nsmul_addY_eq`,
`Mzk1G1R3TwoNsmulYActual.two_nsmul_slope_eq`, Mathlib `preΨ₄`/`b₂..b₈`.
Denominator hypothesis: `d = 2y + a₁x + a₃ ≠ 0`. -/
import tmp.sheaf.xif.paper.Mzk1G1R3TwoNsmulPsy2Actual
import tmp.sheaf.xif.paper.Mzk1G1R3LegendrePsi2TwoActual
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R3Psi2TwoGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulYActual
open LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulPsy2Actual

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- **General-W M2 identity**: `ψ₂(2P)·(2y+a₁x+a₃)³ = preΨ₄(x)` on the curve. -/
theorem psi2AtTwo_mul_cube_general {x y : F}
    (hEq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (hd : 2 * y + W.a₁ * x + W.a₃ ≠ 0) :
    psi2AtTwo W x y * (2 * y + W.a₁ * x + W.a₃) ^ 3 = (W.preΨ 4).eval x := by
  have hy' : y ≠ W.negY x y := by
    intro h
    rw [WeierstrassCurve.Affine.negY] at h
    apply hd
    linear_combination h
  have hslope : W.slope x x y y =
      (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy']
    rw [WeierstrassCurve.Affine.negY]
    congr 1
    ring
  have hy2 : y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ - W.a₁ * x * y - W.a₃ * y :=
    by linear_combination hEq
  have hy3 : y ^ 3 = y * (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ - W.a₁ * x * y - W.a₃ * y) := by
    rw [show y ^ 3 = y * (y ^ 2) by ring, hy2]
  have hy4 : y ^ 4 =
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ - W.a₁ * x * y - W.a₃ * y) ^ 2 := by
    rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, hy2]
  rw [WeierstrassCurve.preΨ_four,
    show W.preΨ₄ = 2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4
      + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2
      + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2) from rfl]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  unfold psi2AtTwo
  rw [two_nsmul_addY_eq W hy', hslope]
  simp only [WeierstrassCurve.Affine.addX]
  have hd2 : (2 * y + W.a₁ * x + W.a₃) ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hd3 : (2 * y + W.a₁ * x + W.a₃) ^ 3 ≠ 0 := pow_ne_zero 3 hd
  field_simp [hd, hd2, hd3]
  ring_nf
  rw [hy4, hy3, hy2]
  ring

#print axioms psi2AtTwo_mul_cube_general
end LeanFormal.IUT.XiFPaper.Mzk1G1R3Psi2TwoGeneralActual