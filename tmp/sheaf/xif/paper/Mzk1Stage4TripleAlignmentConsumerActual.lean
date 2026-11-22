import tmp.sheaf.xif.paper.Mzk1Stage4TripleRegionAlignmentActual

/-! # Mzk1Stage4TripleAlignmentConsumerActual (stage4 lane; consumer, supplemental)

A626 module: consumer of the triple-dependent paper comparison region — conditional ABC
from the canonical `TripleDependentComparison` data, restated through the stage4
alignment.  Canonical file only READ.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleAlignmentConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperComparisonRegionScalingDesignActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleRegionAlignmentActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Conditional ABC from the canonical triple-dependent comparison, via the stage4
alignment instance. -/
theorem stage4_conditional_abc
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) : ABCConjecture :=
  abc_of_tripleComparison T point C

/-- The alignment's region is nonempty-shaped: it is a scaled image of a union. -/
theorem stage4_region_shape (point : Nat → Nat → Nat → S1902Carrier T)
    (a b c : Nat) :
    region (canonicalScaling T point) a b c =
      tripleScale T a b c '' (s1902UnitRegion T ∪ {point a b c}) :=
  canonicalScaling_region_shape T point a b c

#check stage4_conditional_abc
#check stage4_region_shape

end LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleAlignmentConsumerActual
end
