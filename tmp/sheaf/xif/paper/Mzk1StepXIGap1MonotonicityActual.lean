import tmp.sheaf.xif.paper.Mzk1ABCBridgeHeightRegionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap-1 monotonicity (real content)

The named Gap-1 comparison is monotone in epsilon whenever the comparison-region
log-volume is nonnegative. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1MonotonicityActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual

universe u

structure StepXIGap1Comparison (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (epsilon : Real) where
  volume_nonneg : ∀ a b c : Nat, 0 ≤ (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal
  height_le : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal

theorem gap1_monotone (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    {ε ε' : Real} (hle : ε ≤ ε')
    (D : StepXIGap1Comparison X W logShellPoint ε) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε') * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal := by
  intro a b c habc
  have h1 := D.height_le a b c habc
  have hV := D.volume_nonneg a b c
  have h2 : (1 + ε) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
      (1 + ε') * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal :=
    mul_le_mul_of_nonneg_right (by linarith) hV
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1MonotonicityActual

end
