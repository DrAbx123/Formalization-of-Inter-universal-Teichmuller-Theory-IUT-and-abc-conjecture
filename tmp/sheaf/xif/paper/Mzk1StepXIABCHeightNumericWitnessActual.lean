import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi delta numeric witness for the two-gap adapter

The green `exists_delta_sq_le_one_add` at ε = 1 is witnessed explicitly by δ = 1/4. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIABCHeightNumericWitnessActual

open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

theorem stepxi_delta_one_witness : (1 + (1 : Real) / 4) ^ 2 ≤ 1 + 1 := by norm_num

theorem stepxi_delta_one_exists :
    ∃ δ : Real, 0 < δ ∧ (1 + δ) ^ 2 ≤ 1 + 1 :=
  exists_delta_sq_le_one_add (by norm_num)

end LeanFormal.IUT.XiFPaper.Mzk1StepXIABCHeightNumericWitnessActual

end
