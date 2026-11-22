import tmp.sheaf.xif.paper.S2594HpointWiringActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2720BridgeActualObjActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2589DictionaryMinimalActual
open LeanFormal.IUT.XiFPaper.S2594HpointWiringActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- Conditional real-object Cor312 -> ABC bridge: carrier is the actual qVFam tensor
block, hullData is the actual S2586 IQ-hull interface, logShellPoint is the actual
S2588 rational point map, and each per-epsilon comparison is the actual
S2594_epsilonComparison, with the six named inputs kept explicit. -/
noncomputable def bridgeInterfaceS2586
    (hnull : S2589SingletonNull (S2586IQHullLogVolumeInterface (l := l) T b))
    (hval : ∀ a n c : Nat, IsABCTriple a n c →
      ∀ q : Nat, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) →
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) ≤ 1 + eps)
    (hweightvol : ∀ a n c : Nat, IsABCTriple a n c →
      arithmeticWeight (abcRationalPoint a c) ≤
        ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
            (S2588PointMap (l := l) T b) a n c)).toReal)
    (hunit : (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion ≤
      (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (S2586IQHullLogVolumeInterface (l := l) T b).hull + ENNReal.ofReal 0)
    (hsplit : ∀ a n c : Nat, IsABCTriple a n c →
      (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
            (S2588PointMap (l := l) T b) a n c) ≤
        (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          ((S2586IQHullLogVolumeInterface (l := l) T b).scaleShift ''
            (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion) +
          (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
            {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
              (S2588PointMap (l := l) T b a n c)})
    (hptfin : ∀ a n c : Nat, IsABCTriple a n c →
      (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
          (S2588PointMap (l := l) T b a n c)} < ⊤)
    (eps : Real) (heps : 0 < eps) :
    Cor312EpsilonArithmeticComparison
      (S2586IQHullLogVolumeInterface (l := l) T b) eps :=
  S2594_epsilonComparison (l := l) T b hnull (le_of_lt heps)
    (eps := eps) hval hweightvol hunit hsplit hptfin

/-- The full bridge interface built from the six explicit inputs. -/
noncomputable def bridgeInterfaceS2586Full
    (hnull : S2589SingletonNull (S2586IQHullLogVolumeInterface (l := l) T b))
    (hval : ∀ (eps : Real), 0 < eps →
      ∀ a n c : Nat, IsABCTriple a n c →
        ∀ q : Nat, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) →
          max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) ≤ 1 + eps)
    (hweightvol : ∀ a n c : Nat, IsABCTriple a n c →
      arithmeticWeight (abcRationalPoint a c) ≤
        ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
            (S2588PointMap (l := l) T b) a n c)).toReal)
    (hunit : (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion ≤
      (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (S2586IQHullLogVolumeInterface (l := l) T b).hull + ENNReal.ofReal 0)
    (hsplit : ∀ a n c : Nat, IsABCTriple a n c →
      (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
            (S2588PointMap (l := l) T b) a n c) ≤
        (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          ((S2586IQHullLogVolumeInterface (l := l) T b).scaleShift ''
            (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion) +
          (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
            {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
              (S2588PointMap (l := l) T b a n c)})
    (hptfin : ∀ a n c : Nat, IsABCTriple a n c →
      (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
          (S2588PointMap (l := l) T b a n c)} < ⊤) :
    Cor312ToABCBridgeInterface where
  carrier := qVFamTensorBlock T b
  hullData := S2586IQHullLogVolumeInterface (l := l) T b
  epsilonComparison := fun eps heps =>
    bridgeInterfaceS2586 (l := l) T b hnull (hval eps heps) hweightvol hunit
      hsplit hptfin eps heps

/-- Carrier projection of the constructed interface. -/
theorem bridgeInterfaceS2586Full_carrier
    (hnull hval hweightvol hunit hsplit hptfin) :
    (bridgeInterfaceS2586Full (l := l) T b hnull hval hweightvol hunit hsplit
      hptfin).carrier = qVFamTensorBlock T b := rfl

end LeanFormal.IUT.XiFPaper.S2720BridgeActualObjActualAdapted
end
