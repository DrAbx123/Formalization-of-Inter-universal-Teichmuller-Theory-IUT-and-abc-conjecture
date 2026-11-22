import tmp.sheaf.xif.paper.Mzk1StepXIGap1TheoremizationFinalActual
import tmp.sheaf.xif.paper.Mzk1StepXIGap1WiringV2Actual
import tmp.sheaf.xif.paper.Mzk1StepXIGap1FullRatioV2Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap1 theoremization wrap-up

Final read-only wrap-up of the Gap1 theoremization files. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1TheoremizationWrapActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1MonotonicityActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1FullRatioV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1TheoremizationFinalActual

universe u

theorem gap1_wrap_final (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    {ε : Real} (hε : 0 ≤ ε) (D : StepXIGap1Comparison X W logShellPoint ε)
    (a b c : Nat) (habc : IsABCTriple a b c)
    (hV : 0 < (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) :
    Height.logHeight₁ (abcRationalPoint a c) /
        ((1 + ε) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) ≤ 1 :=
  (gap1_final_theoremized X W logShellPoint hε D a b c habc hV).2

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1TheoremizationFinalActual.gap1_final_theoremized
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1WiringV2Actual.gap1_wiring_ratio

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1TheoremizationWrapActual

end
