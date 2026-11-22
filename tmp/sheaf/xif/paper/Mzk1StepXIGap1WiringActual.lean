import tmp.sheaf.xif.paper.Mzk1StepXIGap1ScalingLawV2Actual
import tmp.sheaf.xif.paper.Mzk1StepXIGap1FullRatioV2Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap1 wiring

Wires the epsilon-scaling step to the full-ratio bound: a Gap1 comparison at ε
yields the ratio bound at any ε' ≥ ε. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1WiringActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1MonotonicityActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1ScalingLawV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1FullRatioV2Actual

universe u

theorem gap1_wiring_ratio (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    {ε ε' : Real} (hle : ε ≤ ε') (hε' : 0 ≤ ε')
    (D : StepXIGap1Comparison X W logShellPoint ε)
    (a b c : Nat) (habc : IsABCTriple a b c)
    (hV : 0 < (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) :
    Height.logHeight₁ (abcRationalPoint a c) /
        ((1 + ε') * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) ≤ 1 := by
  have D' : StepXIGap1Comparison X W logShellPoint ε' := gap1_scaling_step X W logShellPoint hle D
  exact gap1_full_ratio X W logShellPoint hε' D' a b c habc hV

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1WiringActual

end
