import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesComponentsShaActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual

/-! # Canonical paper-region gaps as HeightEstimate/VolumeEstimate components -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperRegionGapComponentsShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesComponentsShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- The canonical region log-volume used in the two gaps. -/
noncomputable def regionLogVolume
    (point : Nat → Nat → Nat → S1902Carrier T)
    (a b c : Nat) : Real :=
  (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal

/-- Gap 1 (canonical paper region) is exactly `HeightEstimate`. -/
theorem canonical_gap1_is_heightEstimate
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    HeightEstimate (regionLogVolume T point) :=
  C.height_le_regionVolume

/-- Gap 2 (canonical paper region) is exactly `VolumeEstimate`. -/
theorem canonical_gap2_is_volumeEstimate
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    VolumeEstimate (regionLogVolume T point) ((s1902LogVolume T (s1902Hull T)).toReal) :=
  C.regionVolume_le_weight

/-- The two canonical gaps give the two-estimate package and ABC. -/
theorem abc_of_canonical_gaps_via_components
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) : ABCConjecture :=
  abc_of_components (regionLogVolume T point)
    ((s1902LogVolume T (s1902Hull T)).toReal)
    (canonical_gap1_is_heightEstimate T point C)
    (canonical_gap2_is_volumeEstimate T point C)

#print axioms canonical_gap1_is_heightEstimate
#print axioms canonical_gap2_is_volumeEstimate
#print axioms abc_of_canonical_gaps_via_components

end LeanFormal.IUT.XiFPaper.Mzk1PaperRegionGapComponentsShaActual
