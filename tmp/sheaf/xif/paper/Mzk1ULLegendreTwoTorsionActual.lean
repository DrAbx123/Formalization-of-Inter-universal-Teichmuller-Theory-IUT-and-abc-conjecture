/- Legendre 2-torsion 桥接（第一步）:
  W := legendreWeierstrassCurve lam 的 2-torsion 判据: y=0 时 P+P=0（a1=a3=0, negY x 0 = 0），
  故 (x,0) 的非奇异点属于 torsionBy 2。用于下一步 twoTorsionXOf_legendre = {0,1,lam}。
  donor: Mathlib Affine/Point.lean:675 add_self_of_Y_eq; :606 some_ne_zero;
  Legendre 曲线: LeanFormal/IUT/ABCBridge/Geometry/LegendreWeierstrassCurve.lean。 -/
import LeanFormal.IUT.ABCBridge.Geometry.LegendreWeierstrassCurve
import tmp.sheaf.xif.paper.Mzk1ULTripodalConductorActual
import tmp.sheaf.xif.paper.Mzk1ULTripodalFieldActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.Mzk1ULLegendreTwoTorsionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalConductorActual
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldActual
open WeierstrassCurve

/-- legendre 曲线的 j 等于 jOfLam（用 legendreWeierstrassCurve_j）。 -/
theorem legendre_j_eq_jOfLam (lam : ℂ) (htwo : (2 : ℂ) ≠ 0)
    (h0 : lam ≠ 0) (h1 : lam ≠ 1) [(legendreWeierstrassCurve lam).IsElliptic] :
    (legendreWeierstrassCurve lam).j = jOfLam lam := by
  rw [legendreWeierstrassCurve_j]
  unfold jOfLam
  congr 1 <;> ring

/-- legendre 曲线的 negY x 0 = 0（a1=a3=0）。 -/
theorem legendre_negY_zero (lam x : ℂ) :
    WeierstrassCurve.Affine.negY (legendreWeierstrassCurve lam).toAffine x 0 = 0 := by
  simp [WeierstrassCurve.Affine.negY, legendreWeierstrassCurve_a₁,
    legendreWeierstrassCurve_a₃]

/-- 若 (x,0) 非奇异，则它属于 2-torsion（P+P=0）。 -/
theorem legendre_mem_twoTorsion_of_x (lam x : ℂ) [(legendreWeierstrassCurve lam).IsElliptic]
    (h : (legendreWeierstrassCurve lam).toAffine.Nonsingular x 0) :
    (WeierstrassCurve.Affine.Point.some (W' := (legendreWeierstrassCurve lam).toAffine) x 0 h) ∈
      AddSubgroup.torsionBy (WeierstrassCurve.Affine.Point (W' := (legendreWeierstrassCurve lam).toAffine)) 2 := by
  change (2 : ℕ) • (WeierstrassCurve.Affine.Point.some (W' := (legendreWeierstrassCurve lam).toAffine) x 0 h) = 0
  rw [two_nsmul]
  have hy : (0 : ℂ) = WeierstrassCurve.Affine.negY (legendreWeierstrassCurve lam).toAffine x 0 := by
    rw [legendre_negY_zero]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq (W := (legendreWeierstrassCurve lam).toAffine) hy

/-- 反向: 非零 y 的点不可能是 2-torsion（P+P 的 some 非零）。 -/
theorem legendre_not_mem_twoTorsion_of_y_ne (lam : ℂ) (htwo : (2 : ℂ) ≠ 0)
    [(legendreWeierstrassCurve lam).IsElliptic]
    {x y : ℂ} (h : (legendreWeierstrassCurve lam).toAffine.Nonsingular x y)
    (hy : y ≠ 0) :
    (WeierstrassCurve.Affine.Point.some (W' := (legendreWeierstrassCurve lam).toAffine) x y h) ∉
      AddSubgroup.torsionBy (WeierstrassCurve.Affine.Point (W' := (legendreWeierstrassCurve lam).toAffine)) 2 := by
  intro hmem
  change (2 : ℕ) • (WeierstrassCurve.Affine.Point.some (W' := (legendreWeierstrassCurve lam).toAffine) x y h) = 0 at hmem
  rw [two_nsmul] at hmem
  have hneg : (legendreWeierstrassCurve lam).toAffine.negY x y = -y := by
    simp [WeierstrassCurve.Affine.negY, legendreWeierstrassCurve_a₁,
      legendreWeierstrassCurve_a₃]
  have hyne : y ≠ (legendreWeierstrassCurve lam).toAffine.negY x y := by
    rw [hneg]
    intro h
    have h2 : (2 : ℂ) * y = 0 := by
      have hsum : y + y = 0 := by linear_combination h
      linear_combination hsum
    exact hy (mul_eq_zero.mp h2 |>.resolve_left htwo)
  have hadd := WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (W := (legendreWeierstrassCurve lam).toAffine) (h₁ := h) hyne
  rw [hadd] at hmem
  exact (WeierstrassCurve.Affine.Point.some_ne_zero (W' := (legendreWeierstrassCurve lam).toAffine)
    (WeierstrassCurve.Affine.nonsingular_add h h (fun hxy => hyne hxy.right))) hmem

end LeanFormal.IUT.XiFPaper.Mzk1ULLegendreTwoTorsionActual