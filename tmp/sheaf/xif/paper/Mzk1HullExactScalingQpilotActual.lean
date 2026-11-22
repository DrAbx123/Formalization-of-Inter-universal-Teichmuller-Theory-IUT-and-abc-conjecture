/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1HullExactScalingQpilotActual — hull exact scaling formula (A655)

Exact scaling formula for balls under a scalar direction: for `λ ≠ 0`,
`(x ↦ λ * x) '' closedBall 0 R = closedBall 0 (‖λ‖ * R)` (Mathlib
`smul_closedBall'`), with the Lebesgue-volume corollary.  Basis of the
triple-dependent scaling candidate (`λ = a+b+c+1`). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HullExactScalingQpilotActual

open LeanFormal.IUT
open MeasureTheory
open scoped ENNReal

universe u

/-- Exact scaling formula for closed balls in a normed field. -/
theorem closedBall_scale_exact {k : Type u} [NormedField k]
    (lam : k) (hlam : lam ≠ 0) (R : Real) :
    (fun x : k => lam * x) '' Metric.closedBall (0 : k) R =
      Metric.closedBall (0 : k) (‖lam‖ * R) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy ⊢
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
  · intro hx
    refine ⟨lam⁻¹ * x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx ⊢
      rw [norm_mul, norm_inv]
      have hpos : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
      calc ‖lam‖⁻¹ * ‖x‖ ≤ ‖lam‖⁻¹ * (‖lam‖ * R) :=
            mul_le_mul_of_nonneg_left hx (by positivity)
        _ = R := by field_simp
    · change lam * (lam⁻¹ * x) = x
      rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]

/-- Lebesgue-volume corollary of the exact scaling formula on `Real`. -/
theorem volume_scale_exact (lam : Real) (hlam : lam ≠ 0) (R : Real) :
    volume ((fun x : Real => lam * x) '' Metric.closedBall (0 : Real) R) =
      ENNReal.ofReal (2 * (‖lam‖ * R)) := by
  rw [closedBall_scale_exact lam hlam R, Real.volume_closedBall]

/-- Decision rows for the exact scaling direction. -/
def hullScalingRows : List (String × String) :=
  [ ("exact ball scaling (norm multiplicative)", "PROVED"),
    ("Lebesgue volume scaling corollary", "PROVED"),
    ("triple-dependent lambda = a+b+c+1", "CANDIDATE (mainline tripleScale)") ]

theorem hullScalingRows_length : hullScalingRows.length = 3 := rfl

#check closedBall_scale_exact
#check volume_scale_exact
#check hullScalingRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HullExactScalingQpilotActual
end
