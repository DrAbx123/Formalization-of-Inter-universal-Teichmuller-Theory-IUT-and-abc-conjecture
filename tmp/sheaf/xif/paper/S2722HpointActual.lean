import tmp.sheaf.xif.paper.S2722HunitDActual
import tmp.sheaf.xif.paper.S2590PadicSingletonNullActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2590PadicSingletonNullActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2722HpointActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- The point bound hpoint of S2722_gap2_with_D0 follows directly from the
singleton-null theorem S2590SingletonNull: the point singleton has log-volume
zero, and the arithmetic weight is nonnegative.  No dictionary (S2587) and no
local-log-degree (S2591) input is needed. -/
theorem S2722_hpoint
    (eps : Real) (heps : 0 ≤ eps) :
    ∀ a n c : Nat, IsABCTriple a n c →
      ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
          (S2588PointMap T b a n c)}).toReal
      ≤ (1 + eps) * arithmeticWeight (abcRationalPoint a c) := by
  intro a n c habc
  let W := S2586IQHullLogVolumeInterface (l := l) T b
  change (W.logVolume {W.scaleShift (S2588PointMap T b a n c)}).toReal ≤
    (1 + eps) * arithmeticWeight (abcRationalPoint a c)
  have h0 : W.logVolume {W.scaleShift (S2588PointMap T b a n c)} = 0 :=
    S2590SingletonNull (l := l) T b (W.scaleShift (S2588PointMap T b a n c))
  rw [h0, ENNReal.toReal_zero]
  exact mul_nonneg (by linarith) (arithmeticWeight_nonneg _)

#check S2722_hpoint
#print axioms S2722_hpoint
end LeanFormal.IUT.XiFPaper.S2722HpointActual
end
