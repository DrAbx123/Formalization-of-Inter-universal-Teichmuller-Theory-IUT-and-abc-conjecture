import tmp.sheaf.xif.paper.Mzk1IVThm110FloorNativeHullActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
/-! Exact necessary conditions for floor qSigned = native qSigned.

`floorQSigned = min(hullLog,-1)`, `nativeQSigned = -M`.  Equality forces
`1 ≤ M`; for `1 < M` it forces `hullLog = -M`; for `M = 1` only `-1 ≤ hullLog`.
These are exact obstructions, no fake equality. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorNativeObstructionActual
open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312FloorActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorNativeHullActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (label : Type) [Fintype label] [Nonempty label]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- floor/native equality forces `M ≥ 1`. -/
theorem M_ge_one_of_floor_eq_native
    (h : (signedFloorCertificate (places := places) (tuple := tuple) label μ).qSigned = S3013QSigned T) :
    1 ≤ nativeGlobalQPilotNormalizedLogMagnitude T := by
  have hmin : min (arithmeticTupleCanonicalHullHaarLog places tuple μ) (-1) = S3013QSigned T := by
    change min (arithmeticTupleCanonicalHullHaarLog places tuple μ) (-1) = S3013QSigned T at h
    exact h
  have hle : min (arithmeticTupleCanonicalHullHaarLog places tuple μ) (-1) ≤ -1 :=
    min_le_right _ _
  rw [hmin] at hle
  unfold S3013QSigned nativeGlobalQPilotNormalizedSignedLogVolume at hle
  linarith
/-- For `1 < M`, floor/native equality forces the actual hull log to equal `-M`. -/
theorem hullLog_eq_neg_M_of_floor_eq_native_of_one_lt
    (h : (signedFloorCertificate (places := places) (tuple := tuple) label μ).qSigned = S3013QSigned T)
    (hM : 1 < nativeGlobalQPilotNormalizedLogMagnitude T) :
    arithmeticTupleCanonicalHullHaarLog places tuple μ =
      -nativeGlobalQPilotNormalizedLogMagnitude T := by
  have hmin : min (arithmeticTupleCanonicalHullHaarLog places tuple μ) (-1) = S3013QSigned T := by
    change min (arithmeticTupleCanonicalHullHaarLog places tuple μ) (-1) = S3013QSigned T at h
    exact h
  unfold S3013QSigned nativeGlobalQPilotNormalizedSignedLogVolume at hmin
  by_cases hle : arithmeticTupleCanonicalHullHaarLog places tuple μ ≤ -1
  · rwa [min_eq_left hle] at hmin
  · have hge : -1 ≤ arithmeticTupleCanonicalHullHaarLog places tuple μ := le_of_not_ge hle
    rw [min_eq_right hge] at hmin
    linarith
/-- The hull log decomposes exactly as unit-relative hull volume plus the unit
reference log; hence `hullLog = -M` is equivalent to the unit-relative identity. -/
theorem hullLog_eq_neg_M_iff_unitLog
    (hunit : 0 < (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal) :
    arithmeticTupleCanonicalHullHaarLog places tuple μ =
        -nativeGlobalQPilotNormalizedLogMagnitude T ↔
      arithmeticTupleHullUnitLogVolume places tuple +
          Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
        -nativeGlobalQPilotNormalizedLogMagnitude T := by
  rw [arithmeticTupleCanonicalHullHaarLog,
    arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal]
/-- Exact first missing source in unit-relative form. -/
theorem hullUnitLog_eq_neg_M_sub_unitLog
    (h : arithmeticTupleCanonicalHullHaarLog places tuple μ =
      -nativeGlobalQPilotNormalizedLogMagnitude T) :
    arithmeticTupleHullUnitLogVolume places tuple =
      -nativeGlobalQPilotNormalizedLogMagnitude T -
        Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal := by
  rw [arithmeticTupleCanonicalHullHaarLog,
    arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal] at h
  linarith
/-- Exact obstruction list. -/
def floorNativeObstruction : List String :=
  [ "M >= 1 is necessary for floor qSigned = -M",
    "for M > 1 the actual hull log must equal -M",
    "for M = 1 only hull log >= -1 is forced" ]
theorem floorNativeObstruction_length : floorNativeObstruction.length = 3 := rfl
#check M_ge_one_of_floor_eq_native
#check hullLog_eq_neg_M_of_floor_eq_native_of_one_lt
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorNativeObstructionActual
end
