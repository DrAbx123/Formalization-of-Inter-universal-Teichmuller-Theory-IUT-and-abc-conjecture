/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverseSharpRadius
import LeanFormal.IUT.Foundations.LocalFields.PadicExpLog
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [NormedAlgebra ℚ_[2] K]
/-- p=2 boundary case: `‖x‖ ≤ 1/2` implies `‖log1p x‖ ≤ 1/2`. -/
theorem norm_log1p_le_half {x : K} (hx : ‖x‖ ≤ 1 / 2) :
    ‖log1p x‖ ≤ 1 / 2 := by
  have hrem := norm_logRemainder_sub_le_sharp (K := K) (p := 2) x (0 : K)
    (1 / 2) (by norm_num) (by norm_num [Real.rpow_one]) hx (by simp)
  have hrem2 : ‖logRemainder x‖ ≤ 1 / 2 := by
    have h := hrem
    have h0 : logRemainder (0 : K) = 0 := by simp [logRemainder, log1p_zero]
    rw [h0, sub_zero, sub_zero] at h
    have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hcast] at h
    norm_num [Real.rpow_one] at h
    exact h.trans hx
  calc ‖log1p x‖ = ‖x + logRemainder x‖ := by
        rw [show log1p x = x + logRemainder x by
          unfold logRemainder
          ring]
    _ ≤ max ‖x‖ ‖logRemainder x‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 / 2 := max_le hx hrem2
end LeanFormal.IUT.LocalFieldLogarithm
end