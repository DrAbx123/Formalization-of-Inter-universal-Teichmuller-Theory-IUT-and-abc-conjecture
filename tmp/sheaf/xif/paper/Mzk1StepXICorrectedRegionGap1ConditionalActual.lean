import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi corrected-region conditional Gap1

Conditional Gap1 comparison under the corrected-region volume scaling `V' = c·V`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedRegionGap1ConditionalActual

structure StepXICorrectedGap1Data where
  height : Real
  V : Real
  c : Real
  c_pos : 0 < c
  V_pos : 0 < V
  epsilon : Real
  gap1 : height ≤ (1 + epsilon) * V

theorem correctedRegion_conditional_gap1 (D : StepXICorrectedGap1Data) :
    D.height ≤ ((1 + D.epsilon) / D.c) * (D.c * D.V) := by
  have h := D.gap1
  have hc := D.c_pos
  field_simp
  linarith

theorem correctedRegion_conditional_gap1_iff (D : StepXICorrectedGap1Data) :
    D.height ≤ (1 + D.epsilon) * D.V ↔
      D.height ≤ ((1 + D.epsilon) / D.c) * (D.c * D.V) := by
  constructor
  · intro h
    have hc := D.c_pos
    field_simp
    linarith
  · intro h
    have hc := D.c_pos
    have h2 : ((1 + D.epsilon) / D.c) * (D.c * D.V) = (1 + D.epsilon) * D.V := by
      field_simp
    linarith [h, h2.le, h2.ge]

end LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedRegionGap1ConditionalActual

end
