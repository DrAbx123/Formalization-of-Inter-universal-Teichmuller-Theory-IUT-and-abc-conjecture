/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1HullProductScalingQpilotActual — hull product scaling law (A657)

The coordinatewise scaling law for finite products of closed balls (the hull
product law): `(x ↦ (λ_i • x_i)) '' ∏ closedBall 0 R_i = ∏ closedBall 0 (‖λ_i‖ R_i)`.
This is the exact product version of the 1D `closedBall_scale_exact`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HullProductScalingQpilotActual

universe u

open scoped BigOperators

/-- Product (hull) scaling law: coordinatewise nonzero scaling of a finite product
of closed balls rescales each radius by the coordinate norm. -/
theorem product_closedBall_scale {ι : Type u} [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace Real (E i)]
    (lam : ∀ i, Real) (hlam : ∀ i, lam i ≠ 0) (R : ι → Real) :
    (fun x : (∀ i, E i) => fun i => lam i • x i) ''
        Set.pi Set.univ (fun i => Metric.closedBall (0 : E i) (R i)) =
      Set.pi Set.univ (fun i => Metric.closedBall (0 : E i) (‖lam i‖ * R i)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro i _
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul] at *
    exact le_trans (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hy i (Set.mem_univ i)) (norm_nonneg _)) le_rfl
  · intro hx
    refine ⟨fun i => (lam i)⁻¹ • x i, ?_, ?_⟩
    · intro i _
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, norm_inv]
      have hxi : ‖x i‖ ≤ ‖lam i‖ * R i := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx i (Set.mem_univ i)
      have hpos : 0 < ‖lam i‖ := norm_pos_iff.mpr (hlam i)
      have : ‖lam i‖⁻¹ * ‖x i‖ ≤ ‖lam i‖⁻¹ * (‖lam i‖ * R i) := by
        exact mul_le_mul_of_nonneg_left hxi (by positivity)
      calc ‖lam i‖⁻¹ * ‖x i‖ ≤ ‖lam i‖⁻¹ * (‖lam i‖ * R i) := this
        _ = R i := by field_simp
    · funext i
      change lam i • ((lam i)⁻¹ • x i) = x i
      rw [smul_inv_smul₀ (hlam i)]

#check product_closedBall_scale

end LeanFormal.IUT.XiFPaper.Mzk1HullProductScalingQpilotActual
end
