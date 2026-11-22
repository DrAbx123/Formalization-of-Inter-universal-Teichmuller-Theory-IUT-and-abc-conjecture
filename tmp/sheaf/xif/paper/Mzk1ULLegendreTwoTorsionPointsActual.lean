/- Legendre 2-torsion points: (0,0),(1,0),(lam,0) 非奇异且属于 torsionBy 2。 -/
import tmp.sheaf.xif.paper.Mzk1ULLegendreTwoTorsionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.Mzk1ULLegendreTwoTorsionPointsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ULLegendreTwoTorsionActual
open WeierstrassCurve

theorem legendre_nonsingular_zero (lam : ℂ) (h0 : lam ≠ 0) :
    (legendreWeierstrassCurve lam).toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [legendreWeierstrassCurve_equation_iff]; ring
  · left
    simp [legendreWeierstrassCurve_a₁, legendreWeierstrassCurve_a₂,
      legendreWeierstrassCurve_a₄]
    exact Ne.symm h0

theorem legendre_nonsingular_one (lam : ℂ) (h1 : lam ≠ 1) :
    (legendreWeierstrassCurve lam).toAffine.Nonsingular 1 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [legendreWeierstrassCurve_equation_iff]; ring
  · left
    simp [legendreWeierstrassCurve_a₁, legendreWeierstrassCurve_a₂,
      legendreWeierstrassCurve_a₄]
    have heq : 3 + 2 * (-lam + -1) + lam = 1 - lam := by ring
    rw [heq]
    exact Ne.symm (sub_ne_zero.mpr h1)

theorem legendre_nonsingular_lam (lam : ℂ) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    (legendreWeierstrassCurve lam).toAffine.Nonsingular lam 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [legendreWeierstrassCurve_equation_iff]; ring
  · left
    simp [legendreWeierstrassCurve_a₁, legendreWeierstrassCurve_a₂,
      legendreWeierstrassCurve_a₄]
    have heq : 3 * lam ^ 2 + 2 * (-lam + -1) * lam + lam = lam * (lam - 1) := by ring
    rw [heq]
    exact Ne.symm (mul_ne_zero h0 (sub_ne_zero.mpr h1))

end LeanFormal.IUT.XiFPaper.Mzk1ULLegendreTwoTorsionPointsActual