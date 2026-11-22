import tmp.sheaf.xif.paper.S2590PadicSingletonNullActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import tmp.sheaf.xif.paper.S2586IQHullLogVolumeInstantiationActual
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
open LeanFormal.IUT.XiFPaper.S2589DictionaryMinimalActual
open LeanFormal.IUT.XiFPaper.S2590PadicSingletonNullActual
namespace LeanFormal.IUT.XiFPaper.S2721HpointActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

theorem S2721HpointActual :
    ∀ (eps : Real), 0 < eps →
      ∀ a n c : Nat, IsABCTriple a n c →
        ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
            (S2588PointMap (l := l) T b a n c)}).toReal ≤
          (1 + eps) * arithmeticWeight (abcRationalPoint a c) := by
  intro eps heps a n c habc
  have hnull :
      (S2586IQHullLogVolumeInterface (l := l) T b).logVolume
        {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
          (S2588PointMap (l := l) T b a n c)} = 0 :=
    S2590SingletonNull (l := l) T b (S2588PointMap (l := l) T b a n c)
  rw [hnull, ENNReal.toReal_zero]
  exact mul_nonneg (by linarith) (arithmeticWeight_nonneg _)

#check S2721HpointActual
#print axioms S2721HpointActual

end LeanFormal.IUT.XiFPaper.S2721HpointActual