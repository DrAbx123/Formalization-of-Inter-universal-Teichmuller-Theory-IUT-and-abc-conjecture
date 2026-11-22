import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi corrected Gap1 unconditional V5

Reverse direction and composition for the corrected/unconditional assembly. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap1UnconditionalV5Actual

structure StepXICorrectedGap1Unconditional where
  height : Real
  V : Real
  V' : Real
  epsilon : Real
  V_pos : 0 < V
  V'_pos : 0 < V'
  gap1 : height ≤ (1 + epsilon) * V

theorem corrected_to_original (D : StepXICorrectedGap1Unconditional) :
    D.height ≤ (1 + D.epsilon) * D.V :=
  D.gap1

theorem original_of_corrected (D : StepXICorrectedGap1Unconditional)
    (h : D.height ≤ ((1 + D.epsilon) * D.V / D.V') * D.V') :
    D.height ≤ (1 + D.epsilon) * D.V := by
  rw [div_mul_cancel₀ _ (ne_of_gt D.V'_pos)] at h
  exact h

theorem corrected_unconditional_iff (D : StepXICorrectedGap1Unconditional) :
    D.height ≤ (1 + D.epsilon) * D.V ↔
      D.height ≤ ((1 + D.epsilon) * D.V / D.V') * D.V' := by
  rw [div_mul_cancel₀ _ (ne_of_gt D.V'_pos)]

theorem ratio_unconditional (D : StepXICorrectedGap1Unconditional) :
    D.height / D.V' ≤ ((1 + D.epsilon) * D.V) / D.V' :=
  div_le_div_of_nonneg_right D.gap1 (le_of_lt D.V'_pos)

end LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap1UnconditionalV5Actual

end
