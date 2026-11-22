import tmp.sheaf.xif.paper.Mzk1StepXIABCStage5Gap2ConsumerActual
import tmp.sheaf.xif.paper.Mzk1StepXIABCFormHeightConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi ABC entry points: Gap2 and height-region consumers

Both `ABCConjecture` entries are consumed from already-green stepxi consumers:
* `stepxi_abcStage5_gap2` from the literal Stage-5 estimates;
* `stepxi_abcForm_heightRegion` from the ABC-form additive height bound.
No new named inputs are added here. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIABCEntryPointsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCStage5Gap2ConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCFormHeightConsumerActual

theorem stepxi_abcEntry_gap2 (I : StepXIABCStage5Input) : ABCConjecture :=
  stepxi_abcStage5_gap2 I

theorem stepxi_abcEntry_heightRegion (I : StepXIABCHeightRegionInput) : ABCConjecture :=
  stepxi_abcForm_heightRegion I

end LeanFormal.IUT.XiFPaper.Mzk1StepXIABCEntryPointsActual

end
