import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312FloorActual
import tmp.sheaf.xif.paper.Mzk1IVThm110N5FloorBridgeActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedLogVolume
/-! Exact floor qSigned = native qSigned reduction.

The floor certificate's qSigned is
`min (arithmeticTupleCanonicalHullHaarLog places tuple μ) (-1)`.
It equals the native qSigned `-M` (M = nativeGlobalQPilotNormalizedLogMagnitude)
provided:
* the actual hull log equals `-M`;
* `1 ≤ M` (so the floor `-1` is inactive).
The two arithmetic facts are reduced to these two exact source objects; no fake. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorNativeHullActual
open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312FloorActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5FloorBridgeActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (label : Type) [Fintype label] [Nonempty label]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
/-- The floor qSigned definition unfolds to the min of the actual hull log and -1. -/
theorem signedFloorCertificate_qSigned_eq_min :
    (signedFloorCertificate places tuple label μ).qSigned =
      min (arithmeticTupleCanonicalHullHaarLog places tuple μ) (-1) := rfl
/-- Exact reduction: hull log = `-M` and `1 ≤ M` imply floor qSigned = native qSigned. -/
theorem floorQSigned_eq_native_of_hull
    {T : SourceNativeInitialThetaData.{0} l} [Fintype (Bad (nativePlaceSelection T))]
    (hM : arithmeticTupleCanonicalHullHaarLog places tuple μ =
      -nativeGlobalQPilotNormalizedLogMagnitude T)
    (hMone : 1 ≤ nativeGlobalQPilotNormalizedLogMagnitude T) :
    (signedFloorCertificate places tuple label μ).qSigned = S3013QSigned T := by
  rw [signedFloorCertificate_qSigned_eq_min, hM]
  unfold S3013QSigned nativeGlobalQPilotNormalizedSignedLogVolume
  rw [min_eq_left]
  linarith
/-- The first exact missing actual source object. -/
def floorNativeHullGap : List String :=
  [ "actual hull log arithmeticTupleCanonicalHullHaarLog places tuple μ = -nativeGlobalQPilotNormalizedLogMagnitude T",
    "1 ≤ nativeGlobalQPilotNormalizedLogMagnitude T (floor -1 inactive)" ]
theorem floorNativeHullGap_length : floorNativeHullGap.length = 2 := rfl
#check signedFloorCertificate_qSigned_eq_min
#check floorQSigned_eq_native_of_hull
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorNativeHullActual
end
