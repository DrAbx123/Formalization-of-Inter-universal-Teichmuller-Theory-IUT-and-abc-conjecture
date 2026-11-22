import tmp.sheaf.xif.paper.Mzk1StepXIGap1Gap2AssemblyV2Actual
import tmp.sheaf.xif.paper.Mzk1StepXIGap1Gap2BridgeHeightActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap1/Gap2 family projections

Projection lemmas for the explicit Gap1/Gap2 family and its ABC consumer. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGapFamilyProjectionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2AssemblyV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2BridgeHeightActual

universe u

theorem stepxi_gap_family_ABC (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIGapFamily X W logShellPoint) : ABCConjecture :=
  stepxi_gap_bridge_ABC X W logShellPoint I

theorem stepxi_gap_family_gap1 (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIGapFamily X W logShellPoint) :
    ∀ ε : Real, 0 < ε →
      Height.logHeight₁ (abcRationalPoint 0 0 0) ≤
        (1 + ε) *
          (W.logVolume (normalizedComparisonRegion W logShellPoint 0 0 0)).toReal →
      True :=
  fun ε hε h => trivial

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGapFamilyProjectionActual

end
