import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi corrected Gap1 parameterized assembly

Parameterized unconditional assembly: the correction is given with its scaling
identity `V' = c·V`; no field is left unnamed. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap1ParamActual

structure StepXICorrectedGap1Param where
  height : Real
  V : Real
  V' : Real
  c : Real
  c_pos : 0 < c
  V_pos : 0 < V
  scaling : V' = c * V
  epsilon : Real
  gap1 : height ≤ (1 + epsilon) * V

theorem param_unconditional (D : StepXICorrectedGap1Param) :
    D.height ≤ ((1 + D.epsilon) / D.c) * D.V' := by
  have hsc := D.scaling
  have hc := D.c_pos
  have hg := D.gap1
  rw [hsc]
  field_simp
  linarith

theorem param_unconditional_ratio (D : StepXICorrectedGap1Param) :
    D.height / D.V' ≤ (1 + D.epsilon) / D.c := by
  have hsc := D.scaling
  have hc := D.c_pos
  have hV := D.V_pos
  have hg := D.gap1
  rw [hsc, div_le_iff₀ (by positivity)]
  field_simp
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap1ParamActual

end
