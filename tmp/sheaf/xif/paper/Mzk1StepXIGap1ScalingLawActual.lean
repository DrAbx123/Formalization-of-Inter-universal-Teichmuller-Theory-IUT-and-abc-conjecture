import tmp.sheaf.xif.paper.Mzk1StepXIGap1MonotonicityActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap1 scaling law

Scaling law for the Gap1 comparison: dividing by the epsilon-scaled volume and
monotonicity of the ratio. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1ScalingLawActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1MonotonicityActual

universe u

theorem gap1_scaling_law (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    {ε : Real} (D : StepXIGap1Comparison X W logShellPoint ε)
    (a b c : Nat) (habc : IsABCTriple a b c)
    (hV : 0 < (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) :
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + ε) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ∧
      Height.logHeight₁ (abcRationalPoint a c) /
          ((1 + ε) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) ≤ 1 := by
  have hle := D.height_le a b c habc
  refine ⟨hle, ?_⟩
  rw [div_le_iff₀]
  · linarith
  · have hVnonneg := D.volume_nonneg a b c
    positivity

theorem gap1_scaling_step (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    {ε ε' : Real} (hle : ε ≤ ε')
    (D : StepXIGap1Comparison X W logShellPoint ε) :
    StepXIGap1Comparison X W logShellPoint ε' where
  volume_nonneg := D.volume_nonneg
  height_le := gap1_monotone X W logShellPoint hle D

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1ScalingLawActual

end
