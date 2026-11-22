import tmp.sheaf.xif.paper.S2589DictionaryMinimalActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import tmp.sheaf.xif.paper.S2591PointLocalLogDegreeActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2587Cor312PointMapSkeletonActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2589DictionaryMinimalActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2594HpointWiringActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable {eps : Real} (heps : 0 <= eps)

/-- The `hpoint` shape from the minimal singleton-null dictionary and the H1
valuation bound. -/
theorem S2594_pointBound
    (hnull : S2589SingletonNull (S2586IQHullLogVolumeInterface T b))
    (heps : 0 <= eps)
    (hval : forall a n c : Nat, IsABCTriple a n c ->
      forall q : Nat, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) ->
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) <= 1 + eps) :
    forall a n c : Nat, IsABCTriple a n c ->
      ((S2586IQHullLogVolumeInterface T b).logVolume
        {(S2586IQHullLogVolumeInterface T b).scaleShift
          (S2588PointMap T b a n c)}).toReal <= 
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) :=
  cor312Gap2_pointBound_of_singletonVolume_le_logHeight
    (S2586IQHullLogVolumeInterface T b) (S2588PointMap T b) heps
    (S2589CurrentDictionary_of_singleton_null T b hnull) hval

#check S2594_pointBound

/-- The frozen gap-2 assembly with the wired hpoint input; all other named inputs
are passed through unchanged. -/
noncomputable def S2594_epsilonComparison
    (hnull : S2589SingletonNull (S2586IQHullLogVolumeInterface T b))
    (heps : 0 <= eps)
    (hval : forall a n c : Nat, IsABCTriple a n c ->
      forall q : Nat, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) ->
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) <= 1 + eps)
    (hweightvol : forall a n c : Nat, IsABCTriple a n c ->
      arithmeticWeight (abcRationalPoint a c) <=
        ((S2586IQHullLogVolumeInterface T b).logVolume
          (normalizedComparisonRegion (S2586IQHullLogVolumeInterface T b)
            (S2588PointMap T b) a n c)).toReal)
    (hunit : (S2586IQHullLogVolumeInterface T b).logVolume
        (S2586IQHullLogVolumeInterface T b).unitRegion <=
      (S2586IQHullLogVolumeInterface T b).logVolume
        (S2586IQHullLogVolumeInterface T b).hull + ENNReal.ofReal 0)
    (hsplit : forall a n c : Nat, IsABCTriple a n c ->
      (S2586IQHullLogVolumeInterface T b).logVolume
          (normalizedComparisonRegion (S2586IQHullLogVolumeInterface T b)
            (S2588PointMap T b) a n c) <=
        (S2586IQHullLogVolumeInterface T b).logVolume
          ((S2586IQHullLogVolumeInterface T b).scaleShift ''
            (S2586IQHullLogVolumeInterface T b).unitRegion) +
          (S2586IQHullLogVolumeInterface T b).logVolume
            {(S2586IQHullLogVolumeInterface T b).scaleShift
              (S2588PointMap T b a n c)})
    (hptfin : forall a n c : Nat, IsABCTriple a n c ->
      (S2586IQHullLogVolumeInterface T b).logVolume
        {(S2586IQHullLogVolumeInterface T b).scaleShift
          (S2588PointMap T b a n c)} < ⊤) :
    Cor312EpsilonArithmeticComparison
      (S2586IQHullLogVolumeInterface T b) eps :=
  cor312GapAssembly_epsilonComparisonOfReducedInputs
    (D₁ := 0)
    (S2586IQHullLogVolumeInterface T b) (S2588PointMap T b)
    heps (by norm_num : (0:Real) <= 0) hval hweightvol hunit hsplit hptfin
    (fun a n c habc => by
      simpa using S2594_pointBound T b hnull heps hval a n c habc)

#check S2594_epsilonComparison
end LeanFormal.IUT.XiFPaper.S2594HpointWiringActual
end