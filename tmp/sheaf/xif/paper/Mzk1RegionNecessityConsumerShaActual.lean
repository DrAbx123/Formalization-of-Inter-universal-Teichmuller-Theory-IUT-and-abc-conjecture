import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1PaperRegionGapComponentsShaActual

/-! # Region necessity consumer (canonical paper scaling) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RegionNecessityConsumerShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Consumer: canonical triple-dependent comparison region data gives ABC. -/
theorem region_necessity_consumer
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) : ABCConjecture :=
  abc_of_tripleComparison T point C

#print axioms region_necessity_consumer

end LeanFormal.IUT.XiFPaper.Mzk1RegionNecessityConsumerShaActual
