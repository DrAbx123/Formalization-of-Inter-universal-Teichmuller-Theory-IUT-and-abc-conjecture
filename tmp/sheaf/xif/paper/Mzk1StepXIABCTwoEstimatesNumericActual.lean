import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi ABC two-estimates numeric delta witnesses

Explicit and existential delta-scaling numbers for ε = 1/2, 1, 2. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesNumericActual

open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

theorem delta_half_witness : (1 + (1 : Real) / 8) ^ 2 ≤ 1 + (1 : Real) / 2 := by norm_num

theorem delta_one_witness : (1 + (1 : Real) / 4) ^ 2 ≤ 1 + 1 := by norm_num

theorem delta_two_witness : (1 + (1 : Real) / 4) ^ 2 ≤ 1 + 2 := by norm_num

theorem delta_half_exists : ∃ δ : Real, 0 < δ ∧ (1 + δ) ^ 2 ≤ 1 + (1 : Real) / 2 :=
  exists_delta_sq_le_one_add (by norm_num)

end LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesNumericActual

end
