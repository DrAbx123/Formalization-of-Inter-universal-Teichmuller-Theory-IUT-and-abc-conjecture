/- R3 M2 assembly lemma: the ψ₄ evaluation factorisation.

  `Ψ 4 = C (preΨ 4) * ψ₂` (Mathlib even-n donor) and `ψ₂(x,y) = 2y + a₁x + a₃`
  (donor `WeierstrassCurve.evalDivisionPolynomial_two`) give
  `evalDivisionPolynomial x y 4 = (preΨ 4).eval x * (2y + a₁x + a₃)`.
  Together with henry's zero-equivalence `psi2AtTwo * (2y+a₁x+a₃)^3 = preΨ 4` this yields
  `ψ₂(2P) = 0 ↔ ψ₄(P) = 0` (denominator `2y+a₁x+a₃ ≠ 0`), i.e. M2.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1R3FourNsmulActual
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1G1R3TwoNsmulXActual
import tmp.sheaf.xif.paper.Mzk1G1R3TwoNsmulPsy2Actual
import tmp.sheaf.xif.paper.Mzk1G1R3LegendrePsi2TwoActual
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaTorsionFiveActual

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R3FourCriterionActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1R3FourNsmulActual
open LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulXActual
open LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulPsy2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1R3LegendrePsi2TwoActual

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- **ψ₄ 的求值因式分解**：`ψ₄(x,y) = preΨ₄(x) · (2y + a₁x + a₃)`（在曲线上）。 -/
theorem evalDivisionPolynomial_four_eq {x y : F} (h : W.toAffine.Equation x y) :
    W.evalDivisionPolynomial x y 4 =
      (W.preΨ 4).eval x * (2 * y + W.a₁ * x + W.a₃) := by
  have hψ2 : Polynomial.evalEval x y W.ψ₂ = 2 * y + W.a₁ * x + W.a₃ := by
    have h1 := W.evalDivisionPolynomial_eq_evalEval_Ψ h 2
    rw [WeierstrassCurve.Ψ_two, W.evalDivisionPolynomial_two] at h1
    exact h1.symm
  rw [W.evalDivisionPolynomial_eq_evalEval_Ψ h 4, Psi_four_eq (W := W)]
  rw [Polynomial.evalEval_mul, Polynomial.evalEval_C, hψ2]

#print axioms evalDivisionPolynomial_four_eq

/-- **M2 完成（Legendre）**：`4 • P = 0 ↔ ψ₄(P) = 0`，由 henry 的
    `psi2AtTwo_mul_cube : ψ₂(2P)·(2y)³ = preΨ₄(x)` 与本地 `evalDivisionPolynomial_four_eq` 组合。 -/
theorem legendre_four_nsmul_some_eq_zero_iff (lam : ℂ) {x y : ℂ}
    (hns : (legendreWeierstrassCurve lam).toAffine.Nonsingular x y) (hy : y ≠ 0) :
    (4 : ℤ) • WeierstrassCurve.Affine.Point.some x y hns = 0 ↔
      (legendreWeierstrassCurve lam).evalDivisionPolynomial x y 4 = 0 := by
  have h1 : (legendreWeierstrassCurve lam).a₁ = 0 := rfl
  have h3 : (legendreWeierstrassCurve lam).a₃ = 0 := rfl
  have h6 : (legendreWeierstrassCurve lam).a₆ = 0 := rfl
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hneg : y ≠ (legendreWeierstrassCurve lam).toAffine.negY x y := by
    simp only [WeierstrassCurve.Affine.negY, legendreWeierstrassCurve_a₁,
      legendreWeierstrassCurve_a₃, mul_zero, zero_mul, add_zero, zero_add]
    intro h
    apply hy
    have hsum : (2 : ℂ) * y = 0 := by linear_combination y + h
    rcases mul_eq_zero.mp hsum with hzero | hy0
    · exact absurd hzero h2
    · exact hy0
  have hEq : y ^ 2 = x ^ 3 + (-(1 + lam)) * x ^ 2 + lam * x := by
    have heq := (legendreWeierstrassCurve_equation_iff lam x y).mp hns.1
    linear_combination heq
  -- the two-nsmul value at the doubled point equals psi2AtTwo
  have hP2 := WeierstrassCurve.Affine.Point.two_nsmul_some_x
    (W := legendreWeierstrassCurve lam) hns hneg
  have hquote : (4 : ℤ) • WeierstrassCurve.Affine.Point.some x y hns = 0 ↔
      psi2AtTwo (legendreWeierstrassCurve lam) x y = 0 := by
    rw [four_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_two_nsmul]
    rw [hP2]
    rw [evalDivisionPolynomialAtPoint_some, evalDivisionPolynomial_two]
    simp only [psi2AtTwo]
  constructor
  · intro h4
    have hpsi : psi2AtTwo (legendreWeierstrassCurve lam) x y = 0 := hquote.mp h4
    have hcube := psi2AtTwo_mul_cube (W := legendreWeierstrassCurve lam) h1 h3 h6 h2 hEq hy
    have hpre : ((legendreWeierstrassCurve lam).preΨ 4).eval x = 0 := by
      rw [← hcube, hpsi, zero_mul]
    rw [evalDivisionPolynomial_four_eq (W := legendreWeierstrassCurve lam) hns.1]
    rw [legendreWeierstrassCurve_a₁, legendreWeierstrassCurve_a₃]
    rw [hpre]
    ring
  · intro h4
    have hpre : ((legendreWeierstrassCurve lam).preΨ 4).eval x = 0 := by
      rw [evalDivisionPolynomial_four_eq (W := legendreWeierstrassCurve lam) hns.1] at h4
      rw [legendreWeierstrassCurve_a₁, legendreWeierstrassCurve_a₃] at h4
      rcases mul_eq_zero.mp h4 with hpre | htwo
      · exact hpre
      · exact absurd (by linarith : (2 : ℂ) * y = 0 → False) (by
          intro hzero; exact hy (mul_eq_zero.mp hzero |>.resolve_left h2))
    have hcube := psi2AtTwo_mul_cube (W := legendreWeierstrassCurve lam) h1 h3 h6 h2 hEq hy
    have hpsi : psi2AtTwo (legendreWeierstrassCurve lam) x y = 0 := by
      have hmul : psi2AtTwo (legendreWeierstrassCurve lam) x y * (2 * y) ^ 3 = 0 := by
        rw [hcube, hpre]
      rcases mul_eq_zero.mp hmul with hz | hz
      · exact hz
      · exact absurd hz (pow_ne_zero 3 (by
          intro hzero; exact hy (mul_eq_zero.mp hzero |>.resolve_left h2)))
    exact hquote.mpr hpsi

#print axioms legendre_four_nsmul_some_eq_zero_iff

end LeanFormal.IUT.XiFPaper.Mzk1G1R3FourCriterionActual