import tmp.sheaf.xif.paper.Cor312ComparisonRegionV2Actual
import tmp.sheaf.xif.paper.S2586IQHullLogVolumeInstantiationActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual
noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
namespace LeanFormal.IUT.XiFPaper.Cor312RegionV2S2586
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (bb : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T bb)]
variable [BorelSpace (qVFamTensorBlock T bb)]

noncomputable def Cor312RegionV2S2586
    (comparisonRegion : Nat → Nat → Nat → Set (qVFamTensorBlock T bb))
    (logShellPoint : Nat → Nat → Nat → qVFamTensorBlock T bb)
    (logShellPoint_mem :
      ∀ a b0 c : Nat, logShellPoint a b0 c ∈ comparisonRegion a b0 c)
    (hheight : ∀ (eps : Real), 0 < eps →
      ∀ a b0 c : Nat, IsABCTriple a b0 c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + eps) *
            ((S2586IQHullLogVolumeInterface (l := l) T bb).logVolume
              (comparisonRegion a b0 c)).toReal)
    (hvol : ∀ (eps : Real), 0 < eps →
      ∃ D : Real, ∀ a b0 c : Nat, IsABCTriple a b0 c →
        ((S2586IQHullLogVolumeInterface (l := l) T bb).logVolume
          (comparisonRegion a b0 c)).toReal ≤
          (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
            ((S2586IQHullLogVolumeInterface (l := l) T bb).logVolume
              (S2586IQHullLogVolumeInterface (l := l) T bb).hull).toReal + D) :
    Cor312ToABCBridgeInterfaceV2 where
  carrier := qVFamTensorBlock T bb
  hullData := S2586IQHullLogVolumeInterface (l := l) T bb
  epsilonComparison := fun eps heps =>
    { comparisonRegion := comparisonRegion
      logShellPoint := logShellPoint
      logShellPoint_mem := logShellPoint_mem
      height_le_comparisonRegionVolume := hheight eps heps
      regionVolume_le_normalizedWeight := hvol eps heps }

#check Cor312RegionV2S2586


theorem abcConjecture_of_regionV2
    (comparisonRegion : Nat → Nat → Nat → Set (qVFamTensorBlock T bb))
    (logShellPoint : Nat → Nat → Nat → qVFamTensorBlock T bb)
    (logShellPoint_mem :
      ∀ a b0 c : Nat, logShellPoint a b0 c ∈ comparisonRegion a b0 c)
    (hheight : ∀ (eps : Real), 0 < eps →
      ∀ a b0 c : Nat, IsABCTriple a b0 c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + eps) *
            ((S2586IQHullLogVolumeInterface (l := l) T bb).logVolume
              (comparisonRegion a b0 c)).toReal)
    (hvol : ∀ (eps : Real), 0 < eps →
      ∃ D : Real, ∀ a b0 c : Nat, IsABCTriple a b0 c →
        ((S2586IQHullLogVolumeInterface (l := l) T bb).logVolume
          (comparisonRegion a b0 c)).toReal ≤
          (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
            ((S2586IQHullLogVolumeInterface (l := l) T bb).logVolume
              (S2586IQHullLogVolumeInterface (l := l) T bb).hull).toReal + D) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjectureV2
    (Cor312RegionV2S2586 (l := l) T bb comparisonRegion logShellPoint
      logShellPoint_mem hheight hvol)

#check abcConjecture_of_regionV2
#print axioms abcConjecture_of_regionV2

end LeanFormal.IUT.XiFPaper.Cor312RegionV2S2586