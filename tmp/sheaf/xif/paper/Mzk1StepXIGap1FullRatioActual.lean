import tmp.sheaf.xif.paper.Mzk1StepXIGap1MonotonicityActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap1 full-ratio theorem

The full-ratio form of the Gap1 comparison: height divided by the scaled region
volume is at most 1. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1FullRatioActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1MonotonicityActual

universe u

theorem gap1_full_ratio (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    {ε : Real} (D : StepXIGap1Comparison X W logShellPoint ε)
    (a b c : Nat) (habc : IsABCTriple a b c)
    (hV : 0 < (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) :
    Height.logHeight₁ (abcRationalPoint a c) /
        ((1 + ε) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) ≤ 1 := by
  have h := D.height_le a b c habc
  have hden : 0 < (1 + ε) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal := by
    have hε : 0 ≤ 1 + ε := by linarith [D.volume_nonneg a b c, hV]
    positivity
  rw [div_le_iff₀ hden]
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1FullRatioActual

end
