import tmp.sheaf.xif.paper.S245SourceHullMeasureActual

/-!
# S289: concrete source tensor hull with Measure.addHaar

We instantiate S245 at the actual chosen additive Haar

  MeasureTheory.Measure.addHaar

using the actual IsAddHaarMeasure instance for the arbitrarily chosen positive
compact.  This yields concrete hull open/interior/positive/finite and mu_log
objects, not a parameterized Haar input.  No inequality is stated.
-/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S289SourceHullConcreteHaarActual

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
open LeanFormal.IUT.XiFPaper.S245SourceHullMeasureActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual IsAddHaarMeasure instance for the chosen additive Haar. -/
noncomputable instance sourceQTensorAddHaarIsAddHaar :
    Measure.IsAddHaarMeasure
      (MeasureTheory.Measure.addHaar : Measure (SourceQTensorBlock T b)) :=
  MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure
    (Classical.arbitrary (TopologicalSpace.PositiveCompacts
      (SourceQTensorBlock T b)))

/-- Concrete actual chosen additive Haar on the source tensor block. -/
noncomputable abbrev sourceQTensorConcreteHaar : Measure (SourceQTensorBlock T b) :=
  MeasureTheory.Measure.addHaar

/-- Concrete hull log-volume at the chosen additive Haar. -/
noncomputable def concreteSourceQTensorHullMuLog : ENNReal :=
  sourceQTensorHullMuLog T b (sourceQTensorConcreteHaar T b)

/-- Concrete hull mu_log exact log expression. -/
theorem concreteSourceQTensorHullMuLog_eq_ofReal_log :
    concreteSourceQTensorHullMuLog T b =
      ENNReal.ofReal
        (Real.log
          ((sourceQTensorConcreteHaar T b)
            (sourceQTensorLambdaOHull T b)).toReal) :=
  sourceQTensorHullMuLog_eq_ofReal_log T b (sourceQTensorConcreteHaar T b)

/-- Concrete hull mu_log is finite. -/
theorem concreteSourceQTensorHullMuLog_lt_top :
    concreteSourceQTensorHullMuLog T b < ⊤ :=
  sourceQTensorHullMuLog_lt_top T b (sourceQTensorConcreteHaar T b)

/-- Concrete actual hull object. -/
noncomputable def concreteSourceQTensorHullMeasureObject :
    SourceQTensorHullMeasureObject T b (sourceQTensorConcreteHaar T b) :=
  sourceQTensorHullMeasureObject T b (sourceQTensorConcreteHaar T b)

/-- The concrete hull is open. -/
theorem concreteSourceQTensorHull_open :
    IsOpen (sourceQTensorLambdaOHull T b) :=
  sourceQTensorLambdaOHull_isOpen T b

/-- The concrete hull has nonempty interior. -/
theorem concreteSourceQTensorHull_interior_nonempty :
    (interior (sourceQTensorLambdaOHull T b)).Nonempty :=
  sourceQTensorLambdaOHull_interior_nonempty T b

/-- The concrete hull has positive chosen-Haar mass. -/
theorem concreteSourceQTensorHull_measure_pos :
    0 < sourceQTensorConcreteHaar T b (sourceQTensorLambdaOHull T b) :=
  sourceQTensorLambdaOHull_measure_pos T b (sourceQTensorConcreteHaar T b)

/-- The concrete hull has finite chosen-Haar mass. -/
theorem concreteSourceQTensorHull_measure_lt_top :
    sourceQTensorConcreteHaar T b (sourceQTensorLambdaOHull T b) < ⊤ :=
  sourceQTensorLambdaOHull_measure_lt_top T b (sourceQTensorConcreteHaar T b)

end LeanFormal.IUT.XiFPaper.S289SourceHullConcreteHaarActual

end
