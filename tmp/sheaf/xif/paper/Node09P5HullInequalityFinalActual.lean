import tmp.sheaf.xif.paper.Node09P5HullInequalityActual
import tmp.sheaf.xif.paper.Node09P5NormalizedRegionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicSubmoduleTensor
import Mathlib.Tactic

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.Node09P5HullInequalityActual
open LeanFormal.IUT.XiFPaper.Node09P5NormalizedRegionActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Node09P5HullInequalityFinalActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-! The theta coefficient is nonnegative. -/
theorem qVFamThetaTensorCoefficient_nonneg
    (j : SignedLabel l.value) (i : qVFamTensorV) :
    0 ≤ qVFamThetaTensorCoefficient T b j i := by
  unfold qVFamThetaTensorCoefficient
  exact mul_nonneg (Nat.cast_nonneg _) (qVFamTensorCoefficient_nonneg T b)

/-! Every qVFam theta region is contained in the holomorphic unit reference,
because its fractional coefficients are nonnegative. -/
theorem qVFamThetaTensorRegion_subset_holomorphic
    (j : SignedLabel l.value) :
    qVFamThetaTensorRegion T b j ⊆
      (arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple : Set (qVFamTensorBlock T b)) := by
  intro x hx
  unfold qVFamThetaTensorRegion thetaTensorScaledRegion at hx
  have hle : arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (qVFamThetaTensorCoefficient T b j) ≤
      arithmeticTupleValuationIntegerLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple :=
    arithmeticTupleFractionalLattice_le_valuationInteger
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (fun i => qVFamThetaTensorCoefficient_nonneg T b j i)
  have hmul : arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (qVFamThetaTensorCoefficient T b j) *
      arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple ≤
      arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple := by
    calc
      _ ≤ arithmeticTupleValuationIntegerLattice
            (qVFamTensorPlaces T b) qVFamTensorTuple *
          arithmeticTupleHolomorphicLattice
            (qVFamTensorPlaces T b) qVFamTensorTuple := mul_le_mul' hle le_rfl
      _ = _ := arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple
  exact hmul hx

/-! The finite union of qVFam theta regions is contained in the holomorphic unit region. -/
theorem qVFamThetaTensorRegion_union_subset_holomorphic :
    (⋃ j : SignedLabel l.value, qVFamThetaTensorRegion T b j) ⊆
      (arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple : Set (qVFamTensorBlock T b)) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
  exact qVFamThetaTensorRegion_subset_holomorphic T b j hj

/-! The qVFam theta hull is contained in the holomorphic unit region. -/
theorem qVFamLocalThetaHull_subset_holomorphic :
    qVFamLocalThetaHull T b ⊆
      (arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple : Set (qVFamTensorBlock T b)) := by
  unfold qVFamLocalThetaHull
  have hOclosed : IsClosed
      (arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple : Set (qVFamTensorBlock T b)) := by
    rw [coefficient_arithmeticTupleHolomorphicLattice (p := qVFamTensorP T b)
      (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)]
    exact (isCompact_arithmeticTupleCanonicalRegions
      (qVFamTensorPlaces T b) qVFamTensorTuple).2.isClosed
  exact hOclosed.closure_subset_iff.mpr
    (qVFamThetaTensorRegion_union_subset_holomorphic T b)

/-! The qVFam theta hull is compact. -/
theorem isCompact_qVFamLocalThetaHull :
    IsCompact (qVFamLocalThetaHull T b) := by
  have hOcompact : IsCompact
      (arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple : Set (qVFamTensorBlock T b)) := by
    rw [coefficient_arithmeticTupleHolomorphicLattice (p := qVFamTensorP T b)
      (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)]
    exact (isCompact_arithmeticTupleCanonicalRegions
      (qVFamTensorPlaces T b) qVFamTensorTuple).2
  exact hOcompact.of_isClosed_subset (isClosed_closure)
    (qVFamLocalThetaHull_subset_holomorphic T b)

/-- The holomorphic unit region has positive Haar mass. -/
theorem qVFamHolomorphicLattice_measure_pos :
    0 < Measure.addHaar (arithmeticTupleHolomorphicLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple : Set (qVFamTensorBlock T b)) := by
  rw [coefficient_arithmeticTupleHolomorphicLattice (p := qVFamTensorP T b)
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)]
  exact (measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar).2.1

/-- The qVFam theta hull has finite Haar mass, from compactness. -/
theorem qVFamLocalThetaHull_measure_lt_top :
    Measure.addHaar (qVFamLocalThetaHull T b) < ⊤ :=
  (isCompact_qVFamLocalThetaHull T b).measure_lt_top

/-- Unit-region volume <= theta-hull volume. -/
theorem qVFamUnitRegionVolume_le_thetaHullVolume :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        Measure.addHaar
        (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
          Set (qVFamTensorBlock T b)) ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        Measure.addHaar (qVFamLocalThetaHull T b) :=
  arithmeticTupleNormalizedLogVolume_mono
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar
    (qVFamHolomorphicLattice_subset_thetaHull (l := l) T b)
    (qVFamHolomorphicLattice_measure_pos T b)
    (qVFamLocalThetaHull_measure_lt_top T b)

/-- Final minimal-condition inequality: normalized qPilot volume is at most
the qVFam theta-hull volume, without assuming qPilot positivity or inclusion. -/
theorem qVFamNormalizedQPilotVolume_le_thetaHullVolume :
    qVFamNormalizedQPilotVolume T b ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        Measure.addHaar (qVFamLocalThetaHull T b) :=
  (le_of_lt (qVFamNormalizedQPilotVolume_lt_unitRegion T b)).trans
    (qVFamUnitRegionVolume_le_thetaHullVolume T b)

#print axioms qVFamNormalizedQPilotVolume_le_thetaHullVolume
#print axioms qVFamUnitRegionVolume_le_thetaHullVolume
#print axioms isCompact_qVFamLocalThetaHull

end LeanFormal.IUT.XiFPaper.Node09P5HullInequalityFinalActual
end