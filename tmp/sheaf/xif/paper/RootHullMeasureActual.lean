import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.UnitSmulCanonicalUnitReferenceActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly

/-! # Root hull measure

For the normalized coefficient c_norm and c_root = c_norm/(2l):

* the qPilot normalized region equals u • O_hol for the scaling-data unit u;
* hence it is open compact and has positive finite Haar;
* for c_root >= 0, every root region F(j^2 c_root) O_hol is contained in
  O_hol via arithmeticTupleFractionalLattice_le_valuationInteger and
  arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice;
* the root closure hull is contained in the compact closed O_hol, so it has
  finite Haar; positivity follows from qPilot region containment.

No hpos/hfin assumptions.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.RootHullMeasureActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.UnitSmulCanonicalUnitReferenceActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

/-- Root region coefficient j^2 c_root is nonnegative. -/
theorem rootHalfCoefficient_thetaCoeff_nonneg
    (i : qVFamTensorV) (j : SignedLabel l.value) :
    0 <= (gaussExponent j.1).toNat * rootHalfCoefficient (l := l) T b i := by
  apply mul_nonneg (Nat.cast_nonneg _)
  unfold rootHalfCoefficient
  apply div_nonneg
  · unfold rootNormCoefficient
    exact qVFamNormalizedCoefficient_nonneg (l := l) T b
  · positivity

/-- Every root theta region is contained in O_hol for nonnegative c_root. -/
theorem rootThetaRegion_subset_holomorphic
    (j : SignedLabel l.value) :
    rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootHalfCoefficient (l := l) T b) j ⊆
      arithmeticTupleCanonicalUnitReference
        (qVFamTensorPlaces T b) qVFamTensorTuple := by
  intro x hx
  unfold rootThetaRegion at hx
  have hle : arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun i => (gaussExponent j.1).toNat * rootHalfCoefficient (l := l) T b i) <=
      arithmeticTupleValuationIntegerLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple :=
    arithmeticTupleFractionalLattice_le_valuationInteger
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (fun i => rootHalfCoefficient_thetaCoeff_nonneg (l := l) T b i j)
  have hmul : arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun i => (gaussExponent j.1).toNat * rootHalfCoefficient (l := l) T b i) *
      arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple <=
      arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple := by
    calc
      _ <= arithmeticTupleValuationIntegerLattice
            (qVFamTensorPlaces T b) qVFamTensorTuple *
          arithmeticTupleHolomorphicLattice
            (qVFamTensorPlaces T b) qVFamTensorTuple := mul_le_mul' hle le_rfl
      _ = _ := arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple
  rw [← coefficient_arithmeticTupleHolomorphicLattice
    (qVFamTensorPlaces T b) qVFamTensorTuple]
  exact hmul hx

/-- The root closure hull is contained in O_hol. -/
theorem rootNormHull_subset_holomorphic :
    rootNormHull (l := l) T b ⊆
      arithmeticTupleCanonicalUnitReference
        (qVFamTensorPlaces T b) qVFamTensorTuple := by
  unfold rootNormHull rootThetaHull rootThetaImageSet
  apply closure_minimal
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    exact rootThetaRegion_subset_holomorphic (l := l) T b j hj
  · exact (isCompact_arithmeticTupleCanonicalRegions
      (qVFamTensorPlaces T b) qVFamTensorTuple).2.isClosed

/-- Root hull finite Haar. -/
theorem rootNormHull_measure_lt_top :
    mu (rootNormHull (l := l) T b) < ⊤ :=
  lt_of_le_of_lt (measure_mono (rootNormHull_subset_holomorphic (l := l) T b))
    ((isCompact_arithmeticTupleCanonicalRegions
      (qVFamTensorPlaces T b) qVFamTensorTuple).2.measure_lt_top)

/-- qPilot normalized region equals the scaling-data unit translate of O_hol. -/
theorem qPilotNormRegion_eq_unit_smul :
    qPilotNormRegion (l := l) T b =
      ((arithmeticTupleFractionalGeneratorUnit
        (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootNormScalingData (l := l) T b) :
          qVFamTensorBlock T b) •
        arithmeticTupleCanonicalUnitReference
          (qVFamTensorPlaces T b) qVFamTensorTuple) := by
  unfold qPilotNormRegion qPilotClassicalRegion
  rw [arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul
    (qVFamTensorPlaces T b) qVFamTensorTuple (rootNormScalingData (l := l) T b)]
  rw [arithmeticTupleFractionalGeneratorUnit_coe]

/-- qPilot normalized region positive finite Haar. -/
theorem qPilotNormRegion_measure_pos_lt_top :
    0 < mu (qPilotNormRegion (l := l) T b) ∧
      mu (qPilotNormRegion (l := l) T b) < ⊤ := by
  rw [qPilotNormRegion_eq_unit_smul (l := l) T b]
  exact measure_unit_smul_canonicalUnitReference_pos_lt_top
    (p := qVFamTensorP T b) (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (arithmeticTupleFractionalGeneratorUnit
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (rootNormScalingData (l := l) T b))

/-- Root hull positivity from qPilot region containment. -/
theorem rootNormHull_measure_pos :
    0 < mu (rootNormHull (l := l) T b) :=
  lt_of_lt_of_le (qPilotNormRegion_measure_pos_lt_top (l := l) T b mu).1
    (measure_mono (qPilotNormRegion_subset_rootNormHull
      (l := l) T b))

end LeanFormal.IUT.XiFPaper.RootHullMeasureActual

end