import tmp.sheaf.xif.paper.S2721BridgeSkeletonActual
import tmp.sheaf.xif.paper.S2722HunitDActual
import tmp.sheaf.xif.paper.S2721HpointActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2722HunitDActual
open LeanFormal.IUT.XiFPaper.S2721BridgeSkeletonActual
open LeanFormal.IUT.XiFPaper.S2721HpointActual
namespace LeanFormal.IUT.XiFPaper.S2721BridgeDataActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

noncomputable def S2721BridgeDataActual
    (hheight : ∀ (eps : Real), 0 < eps →
      ∀ a n c : Nat, IsABCTriple a n c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + eps) *
            ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
              (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
                (S2588PointMap (l := l) T b) a n c)).toReal)
    (hpoint : ∀ (eps : Real), 0 < eps →
      ∀ a n c : Nat, IsABCTriple a n c →
        ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
            (S2588PointMap (l := l) T b a n c)}).toReal ≤
          (1 + eps) * arithmeticWeight (abcRationalPoint a c)) :
    S2721BridgeData (qVFamTensorBlock T b) where
  hullData := S2586IQHullLogVolumeInterface (l := l) T b
  logShellPoint := S2588PointMap (l := l) T b
  height_le_normalizedRegionVolume := hheight
  regionVolume_le_normalizedWeight := fun eps heps =>
    S2722_gap2_with_D0 (l := l) T b eps (hpoint eps heps)

#check S2721BridgeDataActual


noncomputable def S2721BridgeActual
    (hheight : ∀ (eps : Real), 0 < eps →
      ∀ a n c : Nat, IsABCTriple a n c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + eps) *
            ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
              (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
                (S2588PointMap (l := l) T b) a n c)).toReal)
    (hpoint : ∀ (eps : Real), 0 < eps →
      ∀ a n c : Nat, IsABCTriple a n c →
        ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
            (S2588PointMap (l := l) T b a n c)}).toReal ≤
          (1 + eps) * arithmeticWeight (abcRationalPoint a c)) :
    Cor312ToABCBridgeInterface :=
  S2721_bridge_of_data
    (S2721BridgeDataActual (l := l) T b hheight hpoint)

#check S2721BridgeActual
#print axioms S2721BridgeDataActual


noncomputable def S2721BridgeDataOnlyHeight
    (hheight : ∀ (eps : Real), 0 < eps →
      ∀ a n c : Nat, IsABCTriple a n c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + eps) *
            ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
              (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
                (S2588PointMap (l := l) T b) a n c)).toReal) :
    S2721BridgeData (qVFamTensorBlock T b) :=
  S2721BridgeDataActual (l := l) T b hheight
    (S2721HpointActual (l := l) T b)

noncomputable def S2721BridgeActualOnlyHeight
    (hheight : ∀ (eps : Real), 0 < eps →
      ∀ a n c : Nat, IsABCTriple a n c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + eps) *
            ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
              (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
                (S2588PointMap (l := l) T b) a n c)).toReal) :
    Cor312ToABCBridgeInterface :=
  S2721_bridge_of_data (S2721BridgeDataOnlyHeight (l := l) T b hheight)

#check S2721BridgeDataOnlyHeight
#check S2721BridgeActualOnlyHeight

end LeanFormal.IUT.XiFPaper.S2721BridgeDataActual