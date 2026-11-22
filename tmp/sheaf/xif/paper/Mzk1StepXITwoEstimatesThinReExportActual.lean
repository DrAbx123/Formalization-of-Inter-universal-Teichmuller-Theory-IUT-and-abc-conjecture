import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoEstimatesReductionActual
import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoGapsFormalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi two-estimates thin re-export

Thin re-export of the green two-gap reduction interface. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXITwoEstimatesThinReExportActual

open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesReductionActual

theorem stepxi_twoestimates_reexport (I : StepXIABCTwoGaps) :
    ABCFormAdditiveHeightBound :=
  stepxi_twoEstimates_reduction I

theorem stepxi_twoestimates_reexport_ABC (I : StepXIABCTwoGaps) :
    ABCConjecture :=
  stepxi_twoEstimates_ABC I

end LeanFormal.IUT.XiFPaper.Mzk1StepXITwoEstimatesThinReExportActual

end
