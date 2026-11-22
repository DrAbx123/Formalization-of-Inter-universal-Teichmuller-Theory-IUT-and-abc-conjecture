import tmp.sheaf.xif.paper.Mzk1StepXIGapCorrespondenceV2Actual
import tmp.sheaf.xif.paper.Mzk1StepXIGap1Gap2BridgeHeightActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi final boundary

Final boundary statement: the two-gap input and the assembled Gap1/Gap2 family both
yield the ABC consequence, with no additional assumptions. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIFinalBoundaryActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGapCorrespondenceV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2AssemblyV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2BridgeHeightActual

universe u

theorem stepxi_final_boundary_twoGaps (I : StepXIABCTwoGaps) : ABCConjecture :=
  stepxi_twoGaps_ABC I

theorem stepxi_final_boundary_gapFamily (X : Type u)
    (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIGapFamily X W logShellPoint) : ABCConjecture :=
  stepxi_gap_bridge_ABC X W logShellPoint I

theorem stepxi_final_boundary_both (I : StepXIABCTwoGaps) :
    ABCFormAdditiveHeightBound ∧ ABCConjecture :=
  ⟨stepxi_twoGaps_abcForm I, stepxi_twoGaps_ABC I⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXIFinalBoundaryActual

end
