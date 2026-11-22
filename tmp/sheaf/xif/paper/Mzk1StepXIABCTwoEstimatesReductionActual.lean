import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoGapsFormalActual
import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoEstimatesIntermediateActual
import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoEstimatesNumericActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi ABC two-estimates reduction interface

Thin re-export of the two-gap input, its ABCForm reduction, and explicit numeric
delta witnesses. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesReductionActual

open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesNumericActual

theorem stepxi_twoEstimates_reduction (I : StepXIABCTwoGaps) :
    ABCFormAdditiveHeightBound := stepxi_twoGaps_abcForm I

theorem stepxi_twoEstimates_ABC (I : StepXIABCTwoGaps) : ABCConjecture :=
  stepxi_twoGaps_ABC I

theorem stepxi_twoEstimates_delta_one :
    (1 + (1 : Real) / 4) ^ 2 ≤ 1 + 1 := delta_one_witness

end LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesReductionActual

end
