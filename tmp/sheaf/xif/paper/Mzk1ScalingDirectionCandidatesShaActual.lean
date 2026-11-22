import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-! # Scaling-direction candidates (research/correction candidates) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ScalingDirectionCandidatesShaActual

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]

/-- Downward scaling candidate: divide by the triple-dependent factor. -/
noncomputable def scaleDown (k : Nat) (x : V) : V :=
  ((k + 1 : Real)⁻¹) • x

/-- Upward scaling candidate: multiply by the triple-dependent factor. -/
noncomputable def scaleUp (k : Nat) (x : V) : V :=
  ((k + 1 : Real)) • x

/-- The two candidates are inverse to each other. -/
theorem scaleDown_scaleUp (k : Nat) (x : V) :
    scaleDown k (scaleUp k x) = x := by
  unfold scaleDown scaleUp
  rw [smul_smul]
  rw [inv_mul_cancel₀]
  · simp
  · positivity

theorem scaleUp_scaleDown (k : Nat) (x : V) :
    scaleUp k (scaleDown k x) = x := by
  unfold scaleUp scaleDown
  rw [smul_smul]
  rw [mul_inv_cancel₀]
  · simp
  · positivity

/-- Downward scaling is norm-nonincreasing for factor >= 1: candidate correction
against the forward direction. -/
theorem norm_scaleDown_le (k : Nat) (x : V) :
    ‖scaleDown k x‖ ≤ ‖x‖ := by
  unfold scaleDown
  rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : Real) ≤ (k + 1 : Real)⁻¹)]
  have hle : (k + 1 : Real)⁻¹ ≤ 1 := by
    have hk1 : (1 : Real) ≤ (k + 1 : Real) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    exact inv_le_one_of_one_le₀ hk1
  calc (k + 1 : Real)⁻¹ * ‖x‖ ≤ 1 * ‖x‖ :=
      mul_le_mul_of_nonneg_right hle (norm_nonneg x)
    _ = ‖x‖ := one_mul _

#print axioms scaleDown_scaleUp
#print axioms norm_scaleDown_le

end LeanFormal.IUT.XiFPaper.Mzk1ScalingDirectionCandidatesShaActual
