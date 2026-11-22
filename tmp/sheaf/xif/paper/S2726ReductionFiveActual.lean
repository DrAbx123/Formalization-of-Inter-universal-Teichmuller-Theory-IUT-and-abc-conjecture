import tmp.sheaf.xif.paper.S2594HpointWiringActual
import tmp.sheaf.xif.paper.S2590PadicSingletonNullActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2726ReductionFiveActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2589DictionaryMinimalActual
open LeanFormal.IUT.XiFPaper.S2590PadicSingletonNullActual
open LeanFormal.IUT.XiFPaper.S2594HpointWiringActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- The five reduction inputs of the S2594 gap assembly: hval, hweightvol,
hunit, hsplit, hptfin.  These are exactly the inputs of
`S2594_epsilonComparison`, exposed as fields so the two Cor312 bridge gaps are
the only remaining interface. -/
structure S2726ReductionFive (eps : Real) (heps : 0 < eps) where
  hval : forall a n c : Nat, IsABCTriple a n c ->
    forall q : Nat, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) ->
      max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) <= 1 + eps
  hweightvol : forall a n c : Nat, IsABCTriple a n c ->
    arithmeticWeight (abcRationalPoint a c) <=
      ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
          (S2588PointMap (l := l) T b) a n c)).toReal
  hunit : (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
      (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion <=
    (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
      (S2586IQHullLogVolumeInterface (l := l) T b).hull + ENNReal.ofReal 0
  hsplit : forall a n c : Nat, IsABCTriple a n c ->
    (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
          (S2588PointMap (l := l) T b) a n c) <=
      (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        ((S2586IQHullLogVolumeInterface (l := l) T b).scaleShift ''
          (S2586IQHullLogVolumeInterface (l := l) T b).unitRegion) +
        (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
            (S2588PointMap (l := l) T b a n c)}
  hptfin : forall a n c : Nat, IsABCTriple a n c ->
    (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
      {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
        (S2588PointMap (l := l) T b a n c)} < ⊤

/-- The five explicit reduction inputs reconstruct the S2594 per-epsilon
comparison. -/
noncomputable def S2726_epsilonComparison
    {eps : Real} {heps : 0 < eps}
    (F : S2726ReductionFive (l := l) T b eps heps) :
    Cor312EpsilonArithmeticComparison
      (S2586IQHullLogVolumeInterface (l := l) T b) eps :=
  S2594_epsilonComparison (l := l) T b
    (S2590SingletonNull (l := l) T b) (le_of_lt heps)
    F.hval F.hweightvol F.hunit F.hsplit F.hptfin

/-- Conditional bridge from the five explicit reduction inputs: carrier is the
actual qVFam tensor block and hullData is the actual S2586 interface. -/
noncomputable def S2726_bridge
    (F : forall (eps : Real) (heps : 0 < eps),
      S2726ReductionFive (l := l) T b eps heps) :
    Cor312ToABCBridgeInterface where
  carrier := qVFamTensorBlock T b
  hullData := S2586IQHullLogVolumeInterface (l := l) T b
  epsilonComparison := fun eps heps =>
    S2726_epsilonComparison (l := l) T b (F eps heps)

/-- The conditional bridge keeps the actual carrier. -/
theorem S2726_bridge_carrier
    (F : forall (eps : Real) (heps : 0 < eps),
      S2726ReductionFive (l := l) T b eps heps) :
    (S2726_bridge (l := l) T b F).carrier = qVFamTensorBlock T b := rfl

#check S2726ReductionFive
#check S2726_epsilonComparison
#check S2726_bridge
#check S2726_bridge_carrier

end LeanFormal.IUT.XiFPaper.S2726ReductionFiveActual
end