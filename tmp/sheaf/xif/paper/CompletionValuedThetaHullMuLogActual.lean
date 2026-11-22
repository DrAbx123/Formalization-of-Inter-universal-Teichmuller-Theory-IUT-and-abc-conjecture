import tmp.sheaf.xif.paper.RootHullMeasureActual

/-! # Completion-valued Theta hull: positive finite Haar and normalized log

The completion-valued model has the actual normalized qVFamily coefficient and
the actual root hull

  rootNormHull = closure(union_j F(j^2 c_root) O_hol),  c_root = c_norm/(2l).

RootHullMeasureActual proves, without hpos/hfin assumptions, that this hull has
positive finite Haar.  This file packages the actual Haar measure and the actual
normalized log

  paperRootCoefficientCompletionHullNormalizedLog
    = arithmeticTupleNormalizedLogVolume places tuple mu rootNormHull,

together with the positivity/finiteness proofs.  This is the actual paper hull
mu_log in the completion-valued model; no equality to a coefficient formula and
no inequality is asserted.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.CompletionValuedThetaHullMuLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

/-- Actual root-coefficient completion hull in the completion-valued model. -/
abbrev paperRootCoefficientCompletionHull : Set (qVFamTensorBlock T b) :=
  rootNormHull (l := l) T b

/-- The actual Haar measure of the root-coefficient completion hull is positive. -/
theorem paperRootCoefficientCompletionHull_measure_pos :
    0 < mu (paperRootCoefficientCompletionHull (l := l) T b) :=
  rootNormHull_measure_pos (l := l) T b mu

/-- The actual Haar measure of the root-coefficient completion hull is finite. -/
theorem paperRootCoefficientCompletionHull_measure_lt_top :
    mu (paperRootCoefficientCompletionHull (l := l) T b) < ⊤ :=
  rootNormHull_measure_lt_top (l := l) T b mu

/-- The actual normalized log-volume of the root-coefficient completion hull. -/
noncomputable def paperRootCoefficientCompletionHullNormalizedLog : Real :=
  arithmeticTupleNormalizedLogVolume
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (paperRootCoefficientCompletionHull (l := l) T b)

/-- The normalized log is exactly the arithmetic normalized volume of the hull. -/
theorem paperRootCoefficientCompletionHullNormalizedLog_eq :
    paperRootCoefficientCompletionHullNormalizedLog (l := l) T b mu =
      arithmeticTupleNormalizedLogVolume
        (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (paperRootCoefficientCompletionHull (l := l) T b) := rfl

/-- Actual completion-valued root-coefficient completion hull mu_log data. -/
structure PaperRootCoefficientCompletionHullMuLogData where
  hull : Set (qVFamTensorBlock T b)
  hull_eq : hull = paperRootCoefficientCompletionHull (l := l) T b
  hull_measure_pos : 0 < mu hull
  hull_measure_lt_top : mu hull < ⊤
  normalizedLog : Real
  normalizedLog_eq : normalizedLog =
    arithmeticTupleNormalizedLogVolume
      (qVFamTensorPlaces T b) qVFamTensorTuple mu hull

/-- The actual completion-valued Theta hull mu_log object. -/
noncomputable def paperRootCoefficientCompletionHullMuLogData :
    PaperRootCoefficientCompletionHullMuLogData (l := l) T b mu where
  hull := paperRootCoefficientCompletionHull (l := l) T b
  hull_eq := rfl
  hull_measure_pos := paperRootCoefficientCompletionHull_measure_pos (l := l) T b mu
  hull_measure_lt_top := paperRootCoefficientCompletionHull_measure_lt_top (l := l) T b mu
  normalizedLog := paperRootCoefficientCompletionHullNormalizedLog (l := l) T b mu
  normalizedLog_eq := rfl

end LeanFormal.IUT.XiFPaper.CompletionValuedThetaHullMuLogActual

end
