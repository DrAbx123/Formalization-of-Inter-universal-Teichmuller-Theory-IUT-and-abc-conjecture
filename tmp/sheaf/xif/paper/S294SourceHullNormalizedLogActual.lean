import tmp.sheaf.xif.paper.S289SourceHullConcreteHaarActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual

/-!
# S294: normalized source hull log-volume object

Relative to the canonical unit reference, define

  unitMass         = addHaar(canonicalUnitReference),
  hullMass         = addHaar(sourceQTensorLambdaOHull),
  normalizedMass   = hullMass / unitMass,
  normalizedLog    = log(hullMass) - log(unitMass).

The unit mass is positive finite, hence normalizedMass is positive finite and
normalizedLog is well-defined.  The exact root/s13 normalization object is
recorded separately: rootCoefficient = order/(2l), tensorCoefficient =
2l * rootCoefficient.  No inequality between the log-volume and coefficients is
asserted.
-/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S294SourceHullNormalizedLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
open LeanFormal.IUT.XiFPaper.S237SourceHullProperActual
open LeanFormal.IUT.XiFPaper.S241SourceHullNoncompactActual
open LeanFormal.IUT.XiFPaper.S245SourceHullMeasureActual
open LeanFormal.IUT.XiFPaper.S289SourceHullConcreteHaarActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual Borel/measurable structure on the source tensor block. -/
noncomputable instance sourceQTensorNormalizedMeasurableSpace :
    MeasurableSpace (SourceQTensorBlock T b) := borel _

noncomputable instance sourceQTensorNormalizedBorelSpace :
    BorelSpace (SourceQTensorBlock T b) := ⟨rfl⟩

/-- Actual additive Haar mass of the canonical unit reference. -/
noncomputable def sourceQTensorUnitReferenceMass : ENNReal :=
  sourceQTensorConcreteHaar T b (sourceQTensorUnitReference T b)

/-- Actual additive Haar mass of the corrected source hull. -/
noncomputable def sourceQTensorHullMass : ENNReal :=
  sourceQTensorConcreteHaar T b (sourceQTensorLambdaOHull T b)

/-- Positive finiteness of the canonical unit reference mass. -/
theorem sourceQTensorUnitReferenceMass_pos_lt_top :
    0 < sourceQTensorUnitReferenceMass T b ∧
      sourceQTensorUnitReferenceMass T b < ⊤ := by
  unfold sourceQTensorUnitReferenceMass sourceQTensorUnitReference
  exact (measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (fun _ (_ : Unit) => sourceThetaPlace T b) (fun _ : PUnit => ())
    (sourceQTensorConcreteHaar T b)).2

/-- Normalized hull mass relative to the canonical unit reference. -/
noncomputable def sourceQTensorHullNormalizedMass : ENNReal :=
  sourceQTensorHullMass T b / sourceQTensorUnitReferenceMass T b

/-- The normalized hull mass is positive. -/
theorem sourceQTensorHullNormalizedMass_pos :
    0 < sourceQTensorHullNormalizedMass T b := by
  unfold sourceQTensorHullNormalizedMass
  exact ENNReal.div_pos
    (concreteSourceQTensorHull_measure_pos T b).ne'
    (sourceQTensorUnitReferenceMass_pos_lt_top T b).2.ne

/-- The normalized hull mass is finite. -/
theorem sourceQTensorHullNormalizedMass_lt_top :
    sourceQTensorHullNormalizedMass T b < ⊤ := by
  unfold sourceQTensorHullNormalizedMass
  exact ENNReal.div_lt_top
    (concreteSourceQTensorHull_measure_lt_top T b).ne
    (sourceQTensorUnitReferenceMass_pos_lt_top T b).1.ne'

/-- Nonzero normalized mass. -/
theorem sourceQTensorHullNormalizedMass_ne_zero :
    sourceQTensorHullNormalizedMass T b ≠ 0 :=
  (sourceQTensorHullNormalizedMass_pos T b).ne'

/-- Normalized hull log-volume. -/
noncomputable def sourceQTensorHullNormalizedLog : Real :=
  Real.log (sourceQTensorHullNormalizedMass T b).toReal

/-- Exact difference formula for the normalized log-volume. -/
theorem sourceQTensorHullNormalizedLog_eq_log_sub_log :
    sourceQTensorHullNormalizedLog T b =
      Real.log (sourceQTensorHullMass T b).toReal -
        Real.log (sourceQTensorUnitReferenceMass T b).toReal := by
  unfold sourceQTensorHullNormalizedLog sourceQTensorHullNormalizedMass
    sourceQTensorHullMass sourceQTensorUnitReferenceMass
  rw [ENNReal.toReal_div]
  have hnum : ((sourceQTensorConcreteHaar T b)
      (sourceQTensorLambdaOHull T b)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr
      ⟨(concreteSourceQTensorHull_measure_pos T b).ne',
        (concreteSourceQTensorHull_measure_lt_top T b).ne⟩
  have hden : ((sourceQTensorConcreteHaar T b)
      (sourceQTensorUnitReference T b)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr
      ⟨(sourceQTensorUnitReferenceMass_pos_lt_top T b).1.ne',
        (sourceQTensorUnitReferenceMass_pos_lt_top T b).2.ne⟩
  rw [Real.log_div hnum hden]

/-- The normalized hull log-volume is well-defined and finite as a real number. -/
theorem sourceQTensorHullNormalizedLog_well_defined :
    sourceQTensorHullNormalizedLog T b =
      Real.log (sourceQTensorHullMass T b).toReal -
        Real.log (sourceQTensorUnitReferenceMass T b).toReal :=
  sourceQTensorHullNormalizedLog_eq_log_sub_log T b

/-- s13/root coefficient normalization object. -/
structure SourceHullS13RootNormalization where
  order : Real
  order_eq : order = ((qVFamily T b).order : Real)
  rootCoefficient : Real
  rootCoefficient_eq : rootCoefficient = qVFamPaperRootCoefficient T b
  rootCoefficient_formula : rootCoefficient = order / (2 * l.value : Real)
  tensorCoefficient : Real
  tensorCoefficient_eq : tensorCoefficient = qVFamTensorCoefficient T b
  tensorCoefficient_formula : tensorCoefficient =
    (2 * l.value : Real) * rootCoefficient

/-- Actual s13/root normalization data. -/
noncomputable def sourceHullS13RootNormalization :
    SourceHullS13RootNormalization T b where
  order := ((qVFamily T b).order : Real)
  order_eq := rfl
  rootCoefficient := qVFamPaperRootCoefficient T b
  rootCoefficient_eq := rfl
  rootCoefficient_formula := rfl
  tensorCoefficient := qVFamTensorCoefficient T b
  tensorCoefficient_eq := rfl
  tensorCoefficient_formula :=
    qVFamTensorCoefficient_eq_twoL_mul_rootCoefficient T b

/-- Actual normalized hull log-volume plus s13/root normalization object. -/
structure SourceHullNormalizedLogObject where
  hull : Set (SourceQTensorBlock T b)
  hull_eq : hull = sourceQTensorLambdaOHull T b
  unitReference : Set (SourceQTensorBlock T b)
  unitReference_eq : unitReference = sourceQTensorUnitReference T b
  normalizedMass : ENNReal
  normalizedMass_eq : normalizedMass = sourceQTensorHullNormalizedMass T b
  normalizedMass_pos : 0 < normalizedMass
  normalizedMass_lt_top : normalizedMass < ⊤
  normalizedLog : Real
  normalizedLog_eq : normalizedLog = sourceQTensorHullNormalizedLog T b
  normalizedLog_formula : normalizedLog =
    Real.log (sourceQTensorHullMass T b).toReal -
      Real.log (sourceQTensorUnitReferenceMass T b).toReal
  rootNormalization : SourceHullS13RootNormalization T b
  rootNormalization_eq : rootNormalization = sourceHullS13RootNormalization T b

/-- Actual normalized hull log-volume object. -/
noncomputable def sourceHullNormalizedLogObject :
    SourceHullNormalizedLogObject T b where
  hull := sourceQTensorLambdaOHull T b
  hull_eq := rfl
  unitReference := sourceQTensorUnitReference T b
  unitReference_eq := rfl
  normalizedMass := sourceQTensorHullNormalizedMass T b
  normalizedMass_eq := rfl
  normalizedMass_pos := sourceQTensorHullNormalizedMass_pos T b
  normalizedMass_lt_top := sourceQTensorHullNormalizedMass_lt_top T b
  normalizedLog := sourceQTensorHullNormalizedLog T b
  normalizedLog_eq := rfl
  normalizedLog_formula := sourceQTensorHullNormalizedLog_eq_log_sub_log T b
  rootNormalization := sourceHullS13RootNormalization T b
  rootNormalization_eq := rfl

end LeanFormal.IUT.XiFPaper.S294SourceHullNormalizedLogActual

end
