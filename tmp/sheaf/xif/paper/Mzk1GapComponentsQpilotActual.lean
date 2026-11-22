/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1GapShapeAuditQpilotActual
import tmp.sheaf.xif.paper.Mzk1LocalEstimateGeneralQpilotActual
import Mathlib.Tactic

/-! # Mzk1GapComponentsQpilotActual — gap components packing (A641)

Pack the two IUT IV estimate components for a fixed bridge comparison datum and
for the mainline triple-dependent comparison region: shapes, region
correspondence, and the absorbed bound. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GapComponentsQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1GapShapeAuditQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1LocalEstimateGeneralQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- The gap components of a fixed bridge comparison datum. -/
structure GapComponents {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) : Prop where
  gap1 : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) * (W.logVolume (C.comparisonRegion a b c)).toReal
  gap2 : ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume (C.comparisonRegion a b c)).toReal ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D
  absorbed : ∀ (h0 : 0 ≤ epsilon) (h1 : epsilon ≤ 1),
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) * ((W.logVolume W.hull).toReal + D)

/-- The gap components from bridge comparison data. -/
noncomputable def gapComponentsOfComparison {X : Type u}
    {W : IQHullLogVolumeInterface X} {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison W epsilon) :
    GapComponents C where
  gap1 := fun a b c habc => C.height_le_normalizedRegionVolume a b c habc
  gap2 := C.regionVolume_le_normalizedWeight
  absorbed := fun h0 h1 => height_bound_of_gapShapes
    (fun a b c habc => C.height_le_normalizedRegionVolume a b c habc)
    C.regionVolume_le_normalizedWeight h0 h1

/-- The gap components of the mainline triple-dependent region. -/
noncomputable def gapComponentsOfTriple
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    RegionGapCorrespondence (s1902IQHullLogVolumeInterface T)
      (paperComparisonRegion T point) :=
  regionCorrespondenceOfTripleComparison T point C

#check gapComponentsOfComparison
#check gapComponentsOfTriple

end LeanFormal.IUT.XiFPaper.Mzk1GapComponentsQpilotActual
end
