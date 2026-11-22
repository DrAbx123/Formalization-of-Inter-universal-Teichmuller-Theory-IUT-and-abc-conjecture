import tmp.sheaf.xif.paper.Mzk1PaperRegionNecessityFinalActual

/-! # Region necessity final consumer (read-only) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityFinalConsumerShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityFinalActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Canonical triple-dependent comparison gives the two final Gap Props. -/
theorem final_gap_props
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    Gap1Prop (s1902IQHullLogVolumeInterface T) (paperComparisonRegion T point) ∧
      Gap2Prop (s1902IQHullLogVolumeInterface T) (paperComparisonRegion T point) :=
  gapPropsOfTripleComparison T point C

/-- Consumer: final Gap Props give ABC. -/
theorem final_abc
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) : ABCConjecture :=
  abc_of_gapProps T point
    (gapPropsOfTripleComparison T point C).1
    (gapPropsOfTripleComparison T point C).2

#print axioms final_abc

end LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityFinalConsumerShaActual
