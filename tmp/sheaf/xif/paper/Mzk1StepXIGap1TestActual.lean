import tmp.sheaf.xif.paper.Mzk1StepXIGap1MonotonicityActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap1 monotonicity test

Concrete ε-chain test for the Gap1 comparison: from ε=0 to ε=1 and to ε=2. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1TestActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1MonotonicityActual

universe u

theorem gap1_test_zero_to_one (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (D : StepXIGap1Comparison X W logShellPoint 0) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + (1 : Real)) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal :=
  gap1_monotone X W logShellPoint (by norm_num) D

theorem gap1_test_zero_to_two (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (D : StepXIGap1Comparison X W logShellPoint 0) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + (2 : Real)) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal :=
  gap1_monotone X W logShellPoint (by norm_num) D

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1TestActual

end
