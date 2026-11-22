import tmp.sheaf.xif.paper.S241SourceHullNoncompactActual
import tmp.sheaf.xif.paper.UnitSmulCanonicalUnitReferenceActual

/-!
# S245: source tensor hull has open interior and positive finite Haar

For any actual additive Haar on the source tensor block, the corrected qUnit
hull is the unit-scaled canonical unit reference.  It is open, compact, has
nonempty interior, positive Haar mass and finite Haar mass.  The exact
haarLogVolume expression is recorded.  No inequality is stated.
-/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S245SourceHullMeasureActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
open LeanFormal.IUT.XiFPaper.S237SourceHullProperActual
open LeanFormal.IUT.XiFPaper.S241SourceHullNoncompactActual
open LeanFormal.IUT.XiFPaper.UnitSmulCanonicalUnitReferenceActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (SourceQTensorBlock T b)]
variable [BorelSpace (SourceQTensorBlock T b)]
variable (mu : Measure (SourceQTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

/-- The corrected hull is the unit-scaled canonical unit reference. -/
theorem sourceQTensorLambdaOHull_eq_unit_smul :
    sourceQTensorLambdaOHull T b =
      (sourceQTensorUnit T b : SourceQTensorBlock T b) •
        sourceQTensorUnitReference T b := by
  rw [sourceQTensorLambdaOHull_eq_image_unitReference T b]
  ext x
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact Set.mem_smul_set.mpr ⟨o, ho, by simp [smul_eq_mul]⟩
  · intro hx
    rw [Set.mem_smul_set] at hx
    rcases hx with ⟨o, ho, hxo⟩
    exact ⟨o, ho, by simpa [smul_eq_mul] using hxo⟩

/-- The corrected hull is open. -/
theorem sourceQTensorLambdaOHull_isOpen :
    IsOpen (sourceQTensorLambdaOHull T b) := by
  rw [sourceQTensorLambdaOHull_eq_unit_smul T b]
  exact isOpen_unit_smul_canonicalUnitReference
    (p := qVFamTensorP T b)
    (places := fun _ (_ : Unit) => sourceThetaPlace T b)
    (tuple := fun _ : PUnit => ())
    (u := sourceQTensorUnit T b)

/-- The corrected hull has nonempty interior. -/
theorem sourceQTensorLambdaOHull_interior_nonempty :
    (interior (sourceQTensorLambdaOHull T b)).Nonempty := by
  have h := (sourceQTensorLambdaOHull_isOpen T b).interior_eq
  rw [h, sourceQTensorLambdaOHull_eq_unit_smul T b]
  refine ⟨0, ?_⟩
  refine ⟨0, ?_, ?_⟩
  · simpa using zero_mem_arithmeticTupleCanonicalUnitReference
      (fun _ (_ : Unit) => sourceThetaPlace T b) (fun _ : PUnit => ())
  · simp

/-- The corrected hull has positive Haar measure. -/
theorem sourceQTensorLambdaOHull_measure_pos :
    0 < mu (sourceQTensorLambdaOHull T b) := by
  have hopen := sourceQTensorLambdaOHull_isOpen T b
  refine hopen.measure_pos mu ⟨0, ?_⟩
  have h0 : (0 : SourceQTensorBlock T b) ∈
      sourceQTensorUnitReference T b := by
    simpa using zero_mem_arithmeticTupleCanonicalUnitReference
      (fun _ (_ : Unit) => sourceThetaPlace T b) (fun _ : PUnit => ())
  rw [sourceQTensorLambdaOHull_eq_unit_smul T b]
  exact ⟨0, h0, by simp⟩

/-- The corrected hull has finite Haar measure. -/
theorem sourceQTensorLambdaOHull_measure_lt_top :
    mu (sourceQTensorLambdaOHull T b) < ⊤ := by
  rw [sourceQTensorLambdaOHull_eq_unit_smul T b]
  exact (isCompact_unit_smul_canonicalUnitReference
    (p := qVFamTensorP T b)
    (places := fun _ (_ : Unit) => sourceThetaPlace T b)
    (tuple := fun _ : PUnit => ())
    (u := sourceQTensorUnit T b)).measure_lt_top

/-- Actual hull Haar log-volume. -/
noncomputable def sourceQTensorHullMuLog : ENNReal :=
  haarLogVolume mu (sourceQTensorLambdaOHull T b)

/-- Exact finite log expression for the hull mu_log. -/
theorem sourceQTensorHullMuLog_eq_ofReal_log :
    sourceQTensorHullMuLog T b mu =
      ENNReal.ofReal
        (Real.log (mu (sourceQTensorLambdaOHull T b)).toReal) := by
  unfold sourceQTensorHullMuLog
  exact haarLogVolume_of_lt_top (sourceQTensorLambdaOHull_measure_lt_top T b mu)

/-- The hull mu_log is finite. -/
theorem sourceQTensorHullMuLog_lt_top :
    sourceQTensorHullMuLog T b mu < ⊤ := by
  rw [sourceQTensorHullMuLog_eq_ofReal_log T b mu]
  exact ENNReal.ofReal_lt_top

/-- Actual positive-finite Haar/mu_log object. -/
structure SourceQTensorHullMeasureObject where
  hull : Set (SourceQTensorBlock T b)
  hull_eq : hull = sourceQTensorLambdaOHull T b
  hull_open : IsOpen hull
  hull_interior_nonempty : (interior hull).Nonempty
  haar : Measure (SourceQTensorBlock T b)
  haar_eq : haar = mu
  haar_pos : 0 < haar hull
  haar_lt_top : haar hull < ⊤
  muLog : ENNReal
  muLog_eq : muLog = sourceQTensorHullMuLog T b mu
  muLog_lt_top : muLog < ⊤
  muLog_log_eq : muLog = ENNReal.ofReal (Real.log (haar hull).toReal)

/-- Actual positive-finite hull measure object. -/
noncomputable def sourceQTensorHullMeasureObject :
    SourceQTensorHullMeasureObject T b mu where
  hull := sourceQTensorLambdaOHull T b
  hull_eq := rfl
  hull_open := sourceQTensorLambdaOHull_isOpen T b
  hull_interior_nonempty := sourceQTensorLambdaOHull_interior_nonempty T b
  haar := mu
  haar_eq := rfl
  haar_pos := sourceQTensorLambdaOHull_measure_pos T b mu
  haar_lt_top := sourceQTensorLambdaOHull_measure_lt_top T b mu
  muLog := sourceQTensorHullMuLog T b mu
  muLog_eq := rfl
  muLog_lt_top := sourceQTensorHullMuLog_lt_top T b mu
  muLog_log_eq := sourceQTensorHullMuLog_eq_ofReal_log T b mu

end LeanFormal.IUT.XiFPaper.S245SourceHullMeasureActual

end
