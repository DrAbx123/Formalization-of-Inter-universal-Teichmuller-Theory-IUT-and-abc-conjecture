import tmp.sheaf.xif.paper.Mzk1StepXIGap1MonotonicityActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap1 theoremization

End-to-end theoremization of the Gap1 comparison from the monotonicity core. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1TheoremizationActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1MonotonicityActual

universe u

theorem gap1_theoremized (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    {ε ε' : Real} (hle : ε ≤ ε')
    (D : StepXIGap1Comparison X W logShellPoint ε) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε') * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal :=
  gap1_monotone X W logShellPoint hle D

theorem gap1_theoremized_self (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    {ε : Real} (D : StepXIGap1Comparison X W logShellPoint ε) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal :=
  gap1_monotone X W logShellPoint le_rfl D

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1TheoremizationActual

end
