/- R3a (2/n): actual E[3]-torsion coordinates of the Legendre family via the division polynomial Ψ₃.

  RECON (Lead): `S1373ZeroCriterionActual` (whitelisted) proves the n=3 group-law correspondence
  (`three_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_three_eq_zero`, `rootSet_three_eq_torsion`,
  `evalDivisionPolynomial_three_eq_zero_iff_three_nsmul_eq_zero`); `EllipticDivisionPolynomialEvaluation`
  gives `evalDivisionPolynomial_eq_eval_preΨ_of_odd`, `evalDivisionPolynomialAtPoint_some`;
  `Mzk1G1F2ThetaDivisionPolynomialsActual` gives `legendreΨ₃` with `legendre_Ψ₃_eq`.
  RESULT: 3-torsion x-coordinate criterion over ℂ for the Legendre family (roots = torsion).
  n = 5/l: no group-law bridge in Mathlib/tree (S1373 header) -> next file uses the actual
  multiplication kernel, not a splitting field. No sorry/axiom. -/
import tmp.sheaf.xif.paper.S1373ZeroCriterionActual
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import LeanFormal.IUT.ABCBridge.Geometry.LegendreWeierstrassCurve
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaDivisionPolynomialsActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTorsionCoordsActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaDivisionPolynomialsActual

variable (lam : ℂ)

/-- E[3] 的 x-坐标集（`legendreΨ₃` 的根）。 -/
def threeTorsionX (lam : ℂ) : Set ℂ := {x : ℂ | (legendreΨ₃ lam).eval x = 0}

/-- `ψ₃` 在 Legendre 曲线上只看 x 且等于 `legendreΨ₃`。 -/
theorem evalDivisionPolynomial_legendre_three {x y : ℂ}
    (h : (legendreWeierstrassCurve lam).toAffine.Equation x y) :
    (legendreWeierstrassCurve lam).evalDivisionPolynomial x y 3 = (legendreΨ₃ lam).eval x := by
  rw [WeierstrassCurve.evalDivisionPolynomial_eq_eval_preΨ_of_odd
    (W := legendreWeierstrassCurve lam) h (by decide : ¬ Even (3 : ℤ))]
  rw [WeierstrassCurve.preΨ_three, legendre_Ψ₃_eq]

/-- **3-挠点判据（x-坐标形式）**：`3 • P = 0 ↔ Ψ₃(x) = 0`。 -/
theorem legendre_three_nsmul_eq_zero_iff {x y : ℂ}
    (hns : (legendreWeierstrassCurve lam).toAffine.Nonsingular x y) :
    (3 : ℤ) • WeierstrassCurve.Affine.Point.some x y hns = 0 ↔
      (legendreΨ₃ lam).eval x = 0 := by
  have hD := WeierstrassCurve.evalDivisionPolynomial_three_eq_zero_iff_three_nsmul_eq_zero
    (W := legendreWeierstrassCurve lam) hns
  have he := evalDivisionPolynomial_legendre_three lam hns.1
  constructor
  · intro h3
    have h0 : (legendreWeierstrassCurve lam).evalDivisionPolynomial x y 3 = 0 := hD.mpr h3
    rwa [he] at h0
  · intro hPsi
    apply hD.mp
    rw [he]
    exact hPsi

/-- `evalDivisionPolynomialAtPoint 3` 的根 ↔ `legendreΨ₃` 的根。 -/
theorem legendre_evalDivisionPolynomialAtPoint_three_eq_zero_iff {x y : ℂ}
    (hns : (legendreWeierstrassCurve lam).toAffine.Nonsingular x y) :
    (legendreWeierstrassCurve lam).evalDivisionPolynomialAtPoint 3
        (WeierstrassCurve.Affine.Point.some x y hns) = 0 ↔
      (legendreΨ₃ lam).eval x = 0 := by
  rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some
    (W := legendreWeierstrassCurve lam) x y hns 3]
  rw [evalDivisionPolynomial_legendre_three lam hns.1]

#print axioms evalDivisionPolynomial_legendre_three
#print axioms legendre_three_nsmul_eq_zero_iff
#print axioms legendre_evalDivisionPolynomialAtPoint_three_eq_zero_iff

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTorsionCoordsActual