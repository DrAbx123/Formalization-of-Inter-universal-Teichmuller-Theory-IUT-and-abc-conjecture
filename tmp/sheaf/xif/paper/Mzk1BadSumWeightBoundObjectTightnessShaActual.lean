import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesComponentsShaActual

/-! # BadSumWeightBound <-> ABC object tightness (read-only) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightBoundObjectTightnessShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesComponentsShaActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- The corrected-region Gap2 shape is exactly the volume-estimate component of the
two-estimate package for the corrected-region log-volume. -/
theorem correctedGap2_iff_volumeEstimate
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) :
    CorrectedGap2Shape T point eN ↔
    VolumeEstimate
      (fun a b c => (s1902LogVolume T
        (badInvScale T (eN a b c) '' (s1902UnitRegion T ∪ {point a b c}))).toReal)
      ((s1902LogVolume T (s1902Hull T)).toReal) :=
  Iff.rfl

/-- Object tightness: corrected-region Gap1 + corrected-region Gap2 give ABC. -/
theorem abc_of_correctedGap1_and_gap2
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (h1 : HeightEstimate
      (fun a b c => (s1902LogVolume T
        (badInvScale T (eN a b c) '' (s1902UnitRegion T ∪ {point a b c}))).toReal))
    (h2 : CorrectedGap2Shape T point eN) : ABCConjecture :=
  abc_of_components
    (fun a b c => (s1902LogVolume T
      (badInvScale T (eN a b c) '' (s1902UnitRegion T ∪ {point a b c}))).toReal)
    ((s1902LogVolume T (s1902Hull T)).toReal) h1
    ((correctedGap2_iff_volumeEstimate T point eN).mp h2)

#print axioms correctedGap2_iff_volumeEstimate
#print axioms abc_of_correctedGap1_and_gap2

end LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightBoundObjectTightnessShaActual
