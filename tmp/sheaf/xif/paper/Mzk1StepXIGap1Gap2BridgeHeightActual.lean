import tmp.sheaf.xif.paper.Mzk1StepXIGap1Gap2AssemblyV2Actual
import tmp.sheaf.xif.paper.Mzk1ABCEntryQpilotActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap1/Gap2 bridge ABC consumer

Consumes the V2 Gap1/Gap2 assembled bridge interface to obtain ABCConjecture. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2BridgeHeightActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2AssemblyV2Actual

universe u

theorem stepxi_gap_bridge_ABC (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIGapFamily X W logShellPoint) : ABCConjecture :=
  abcEntry_abcConjecture (stepxiBridgeOfGaps X W logShellPoint I)

theorem stepxi_gap_bridge_heightBound (X : Type u)
    (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIGapFamily X W logShellPoint) :
    ∀ ε : Real, 0 < ε → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A :=
  stepxiBridgeOfGaps_heightBound X W logShellPoint I

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2BridgeHeightActual

end
