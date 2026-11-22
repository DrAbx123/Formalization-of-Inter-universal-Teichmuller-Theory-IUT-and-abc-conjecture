import tmp.sheaf.xif.paper.Mzk1StepXICorrectedGap1UnconditionalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi corrected Gap1 unconditional V2

Stronger unconditional forms: explicit correction `V'/V`, ratio bound by `(1+ε)/c`,
and the exact scaling identity. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap1UnconditionalV2Actual

open LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap1UnconditionalActual

theorem correction_eq_ratio (D : StepXICorrectedGap1Unconditional) :
    D.correction = D.V' / D.V := rfl

theorem corrected_gap1_ratio_by_correction (D : StepXICorrectedGap1Unconditional) :
    D.height / D.V' ≤ (1 + D.epsilon) / D.correction := by
  have h := D.gap1
  have hV := D.V_pos
  have hV' := D.V'_pos
  unfold StepXICorrectedGap1Unconditional.correction
  rw [div_le_div_iff_of_pos_right hV']
  rw [div_eq_mul_inv]
  field_simp
  linarith

theorem correction_scaling_identity (D : StepXICorrectedGap1Unconditional) :
    D.correction * D.V = D.V' := by
  unfold StepXICorrectedGap1Unconditional.correction
  field_simp [D.V_pos.ne']

end LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap1UnconditionalV2Actual

end
