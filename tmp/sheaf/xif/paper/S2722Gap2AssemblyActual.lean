import tmp.sheaf.xif.paper.S2722HunitDActual
import tmp.sheaf.xif.paper.S2595UnconditionalDictionaryActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S2722Gap2AssemblyActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2595UnconditionalDictionaryActual
open LeanFormal.IUT.XiFPaper.S2722HunitDActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- Per-epsilon comparison with only hval and hweightvol as named gap inputs.
The gap2 constant is the actual D0 from S2722 (not hardcoded 0), and hpoint is
discharged by S2595_hpoint from hval. -/
noncomputable def S2722_epsilonComparisonS2586
    (eps : Real) (heps : 0 < eps)
    (hval : ∀ a n c : Nat, IsABCTriple a n c →
      ∀ q : Nat, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) →
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) ≤ 1 + eps)
    (hweightvol : ∀ a n c : Nat, IsABCTriple a n c →
      arithmeticWeight (abcRationalPoint a c) ≤
        ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
            (S2588PointMap (l := l) T b) a n c)).toReal) :
    Cor312EpsilonArithmeticComparison
      (S2586IQHullLogVolumeInterface (l := l) T b) eps where
  logShellPoint := S2588PointMap (l := l) T b
  height_le_normalizedRegionVolume :=
    cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound
      (S2586IQHullLogVolumeInterface (l := l) T b)
      (S2588PointMap (l := l) T b) (le_of_lt heps) hval hweightvol
  regionVolume_le_normalizedWeight :=
    S2722_gap2_with_D0 (l := l) T b eps
      (S2595_hpoint (l := l) T b (le_of_lt heps) hval)

/-- Full bridge over the actual S2586/S2588 carrier with exactly two named gap
inputs: hval and hweightvol.  hunit/hsplit/hptfin are actual (S2722/S2720). -/
noncomputable def S2722_bridgeS2586
    (hval : ∀ (eps : Real), 0 < eps →
      ∀ a n c : Nat, IsABCTriple a n c →
        ∀ q : Nat, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) →
          max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) ≤ 1 + eps)
    (hweightvol : ∀ a n c : Nat, IsABCTriple a n c →
      arithmeticWeight (abcRationalPoint a c) ≤
        ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          (normalizedComparisonRegion (S2586IQHullLogVolumeInterface (l := l) T b)
            (S2588PointMap (l := l) T b) a n c)).toReal) :
    Cor312ToABCBridgeInterface where
  carrier := qVFamTensorBlock T b
  hullData := S2586IQHullLogVolumeInterface (l := l) T b
  epsilonComparison := fun eps heps =>
    S2722_epsilonComparisonS2586 (l := l) T b eps heps
      (hval eps heps) hweightvol

theorem S2722_bridgeS2586_carrier
    (hval hweightvol) :
    (S2722_bridgeS2586 (l := l) T b hval hweightvol).carrier
      = qVFamTensorBlock T b := rfl

#check S2722_epsilonComparisonS2586
#check S2722_bridgeS2586
#check S2722_bridgeS2586_carrier
#print axioms S2722_epsilonComparisonS2586
#print axioms S2722_bridgeS2586
end LeanFormal.IUT.XiFPaper.S2722Gap2AssemblyActual
end
