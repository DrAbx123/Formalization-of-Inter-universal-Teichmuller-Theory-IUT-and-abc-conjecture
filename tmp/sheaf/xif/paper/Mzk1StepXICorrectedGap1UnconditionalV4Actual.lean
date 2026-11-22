import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi corrected Gap1 unconditional V3

Robust algebra for the unconditional corrected-Gap1 assembly. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap1UnconditionalV4Actual

structure StepXICorrectedGap1Unconditional where
  height : Real
  V : Real
  V' : Real
  epsilon : Real
  V_pos : 0 < V
  V'_pos : 0 < V'
  gap1 : height ≤ (1 + epsilon) * V

theorem corrected_gap1_unconditional (D : StepXICorrectedGap1Unconditional) :
    D.height ≤ ((1 + D.epsilon) * D.V / D.V') * D.V' := by
  rw [div_mul_cancel₀ _ (ne_of_gt D.V'_pos)]
  exact D.gap1

theorem corrected_gap1_unconditional_ratio (D : StepXICorrectedGap1Unconditional) :
    D.height / D.V' ≤ ((1 + D.epsilon) * D.V) / D.V' := by
  exact div_le_div_of_nonneg_right D.gap1 (le_of_lt D.V'_pos)

theorem corrected_gap1_unconditional_iff (D : StepXICorrectedGap1Unconditional) :
    D.height ≤ (1 + D.epsilon) * D.V ↔
      D.height / D.V' ≤ ((1 + D.epsilon) * D.V) / D.V' := by
  exact (div_le_div_iff_of_pos_right D.V'_pos).symm

end LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap1UnconditionalV4Actual

end
