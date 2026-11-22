import tmp.sheaf.xif.paper.Mzk1StepXIGap1Gap2BridgeHeightActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi gap-bridge thin re-export V2

Thin re-export of the green Gap1/Gap2 bridge. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGapBridgeThinReExportV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2AssemblyV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2BridgeHeightActual

universe u

theorem stepxi_gapbridge_v2_height (X : Type u)
    (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIGapFamily X W logShellPoint) :
    ∀ ε : Real, 0 < ε → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A :=
  stepxi_gap_bridge_heightBound X W logShellPoint I

theorem stepxi_gapbridge_v2_ABC (X : Type u)
    (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIGapFamily X W logShellPoint) : ABCConjecture :=
  stepxi_gap_bridge_ABC X W logShellPoint I

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGapBridgeThinReExportV2Actual

end
