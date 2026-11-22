/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1ABCEstimatesArithmeticQpilotActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual

/-! # Mzk1LocalEstimateGeneralQpilotActual — general region gap correspondence + mainline

A637 (qpilot lane): generalize the two IUT IV estimate shapes to an arbitrary
region family (`RegionGapCorrespondence`), consume them via the absorbed-bound
arithmetic, and instantiate on the mainline canonical triple-dependent paper
comparison region (read-only import). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LocalEstimateGeneralQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- Gap correspondence for an arbitrary region family (the two IUT IV estimate
shapes). -/
structure RegionGapCorrespondence {X : Type u} (W : IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X) : Prop where
  height_le_region : ∀ epsilon : Real, 0 < epsilon →
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * (W.logVolume (region a b c)).toReal
  region_le_weight : ∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (region a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D

/-- Absorbed height bound from a region gap correspondence. -/
theorem height_bound_of_regionCorrespondence {X : Type u}
    {W : IQHullLogVolumeInterface X} {region : Nat → Nat → Nat → Set X}
    (E : RegionGapCorrespondence W region)
    {epsilon : Real} (hpos : 0 < epsilon) (h1 : epsilon ≤ 1) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) * ((W.logVolume W.hull).toReal + D) := by
  obtain ⟨D, hD⟩ := E.region_le_weight epsilon hpos
  refine ⟨D, fun a b c habc => ?_⟩
  have hge1 := E.height_le_region epsilon hpos a b c habc
  have hge2 := hD a b c habc
  have hw : (0 : Real) ≤ arithmeticWeight (abcRationalPoint a c) :=
    arithmeticWeight_nonneg _
  exact height_le_absorbed (le_of_lt hpos) h1 hw
    (height_le_of_twoEstimates (le_of_lt hpos) hge1 hge2)

/-- The mainline canonical region gap correspondence from `TripleDependentComparison`. -/
noncomputable def regionCorrespondenceOfTripleComparison
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    RegionGapCorrespondence (s1902IQHullLogVolumeInterface T)
      (paperComparisonRegion T point) where
  height_le_region := fun epsilon hepsilon a b c habc =>
    C.height_le_regionVolume epsilon hepsilon a b c habc
  region_le_weight := C.regionVolume_le_weight

/-- Height bound from the mainline triple-dependent comparison (absorbed form). -/
theorem height_bound_of_tripleComparison
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point)
    {epsilon : Real} (hpos : 0 < epsilon) (h1 : epsilon ≤ 1) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) * ((s1902LogVolume T (s1902Hull T)).toReal + D) :=
  height_bound_of_regionCorrespondence
    (regionCorrespondenceOfTripleComparison T point C) hpos h1

#check height_bound_of_regionCorrespondence
#check height_bound_of_tripleComparison

end LeanFormal.IUT.XiFPaper.Mzk1LocalEstimateGeneralQpilotActual
end
