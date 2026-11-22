import tmp.sheaf.xif.paper.S2337TwoTorsionCorrectActual

noncomputable section
open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S2335TwoTorsionRootActual
open LeanFormal.IUT.XiFPaper.S2337TwoTorsionCorrectActual

namespace TestTwoTorsion

variable {R : Type*} [Field R] (W : WeierstrassCurve R)

theorem test (h2 : (2 : R) ≠ 0) (x : R)
    (hx : W.twoTorsionPolynomial.toPoly.eval x = 0) :
    WeierstrassCurve.Affine.Equation W x (S2337Y W x) := by
  have h4 : (W.a₁ * x + W.a₃) ^ 2 +
      4 * (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    have h := S2335TwoTorsionPolynomial_eval W x
    rw [h] at hx
    exact hx
  rw [WeierstrassCurve.Affine.equation_iff]
  rw [S2337Y]
  field_simp [h2]
  linear_combination -h4

end TestTwoTorsion
