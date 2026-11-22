/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1LocalEstimateConsumerQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCEntryGap2QpilotActual
import Mathlib.Tactic

/-! # Mzk1GapCorrespondenceAuditQpilotActual — Gap1/Gap2 substantive correspondence

A631 (qpilot lane): the bridge comparison fields ARE the two IUT IV local-estimate
correspondences.  We construct `LocalEstimateGapCorrespondence` from a bridge
`Cor312EpsilonArithmeticComparison`, and record the exact field-level equivalences. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GapCorrespondenceAuditQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1LocalEstimateConsumerQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

/-- Fixed-ε local-estimate gap correspondence (the bridge data's two fields). -/
structure GapCorrespondenceAt {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (epsilon : Real) : Prop where
  gap1 : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) * localEstimateOfRegion W logShellPoint a b c
  gap2 : ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
    localEstimateOfRegion W logShellPoint a b c ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D

/-- **Construct the fixed-ε gap correspondence from bridge data.** -/
noncomputable def correspondenceAtOfComparison {X : Type u}
    {W : IQHullLogVolumeInterface X} {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison W epsilon) :
    GapCorrespondenceAt W C.logShellPoint epsilon where
  gap1 := fun a b c habc => by
    simpa [localEstimateOfRegion, normalizedComparisonRegion] using
      C.height_le_normalizedRegionVolume a b c habc
  gap2 := by
    obtain ⟨D, hD⟩ := C.regionVolume_le_normalizedWeight
    refine ⟨D, fun a b c habc => ?_⟩
    simpa [localEstimateOfRegion, normalizedComparisonRegion] using hD a b c habc

/-- Gap 1 is exactly the bridge height-comparison field. -/
theorem gap1_iff_bridge {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * localEstimateOfRegion W C.logShellPoint a b c) ↔
      (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (W.logVolume (C.comparisonRegion a b c)).toReal) :=
  ⟨fun h a b c habc => by simpa [localEstimateOfRegion, Cor312EpsilonArithmeticComparison.comparisonRegion] using h a b c habc,
   fun h a b c habc => by simpa [localEstimateOfRegion, Cor312EpsilonArithmeticComparison.comparisonRegion] using h a b c habc⟩

/-- Gap 2 is exactly the bridge region-volume field. -/
theorem gap2_iff_bridge {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    (∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
        localEstimateOfRegion W C.logShellPoint a b c ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
            (W.logVolume W.hull).toReal + D) ↔
      (∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
        (W.logVolume (C.comparisonRegion a b c)).toReal ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
            (W.logVolume W.hull).toReal + D) :=
  ⟨fun ⟨D, hD⟩ => ⟨D, fun a b c habc => by
      have := hD a b c habc
      simpa [localEstimateOfRegion, Cor312EpsilonArithmeticComparison.comparisonRegion] using this⟩,
   fun ⟨D, hD⟩ => ⟨D, fun a b c habc => by
      have := hD a b c habc
      simpa [localEstimateOfRegion, Cor312EpsilonArithmeticComparison.comparisonRegion] using this⟩⟩

/-- Audit rows: gap correspondence. -/
def gapCorrespondenceRows : List (String × String) :=
  [ ("Gap1 = bridge height comparison", "PROVED (iff)"),
    ("Gap2 = bridge region-volume", "PROVED (iff)"),
    ("GapCorrespondenceAt from bridge data", "PROVED (constructed)") ]

theorem gapCorrespondenceRows_length : gapCorrespondenceRows.length = 3 := rfl

#check correspondenceAtOfComparison
#check gap1_iff_bridge
#check gap2_iff_bridge

end LeanFormal.IUT.XiFPaper.Mzk1GapCorrespondenceAuditQpilotActual
end
