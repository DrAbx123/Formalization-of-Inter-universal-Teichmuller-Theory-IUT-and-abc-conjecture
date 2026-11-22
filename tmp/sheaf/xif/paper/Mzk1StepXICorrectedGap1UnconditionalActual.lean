import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi corrected Gap1 unconditional assembly

Assembly where the correction factor is not a named input but computed as `V'/V`,
so the corrected-region Gap1 bound is unconditional in `c`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap1UnconditionalActual

structure StepXICorrectedGap1Unconditional where
  height : Real
  V : Real
  V' : Real
  epsilon : Real
  V_pos : 0 < V
  V'_pos : 0 < V'
  gap1 : height ≤ (1 + epsilon) * V

def StepXICorrectedGap1Unconditional.correction (D : StepXICorrectedGap1Unconditional) : Real :=
  D.V' / D.V

theorem correction_pos (D : StepXICorrectedGap1Unconditional) :
    0 < D.correction := div_pos D.V'_pos D.V_pos

theorem corrected_gap1_unconditional (D : StepXICorrectedGap1Unconditional) :
    D.height ≤ ((1 + D.epsilon) * D.V / D.V') * D.V' := by
  have h := D.gap1
  have hV' := D.V'_pos
  field_simp
  linarith

theorem corrected_gap1_unconditional_ratio (D : StepXICorrectedGap1Unconditional) :
    D.height / D.V' ≤ (1 + D.epsilon) * D.V / D.V' := by
  have h := D.gap1
  have hV' := D.V'_pos
  rw [div_le_div_iff_of_pos_right hV']
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap1UnconditionalActual

end
