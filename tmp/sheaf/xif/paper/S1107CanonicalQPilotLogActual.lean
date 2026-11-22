import tmp.sheaf.xif.paper.S1091QPilotQ1UPositivityActual
import tmp.sheaf.xif.paper.S1096Q1ULogSupplyActual

/-! # S1107: canonical qPilot log and qParameter card / source link

canonicalQPilotLog is filled by the S1091 log-Haar on qPilotQ1URegion.  Its
closed formula is actual conditional on the S1096 coefficient gap.  The
qParameter card is actual conditional on nonzero canonical log; the source
link/finite links remain exact.  No fake equality and no unconditional card. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1107CanonicalQPilotLogActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open LeanFormal.IUT.XiFPaper.S1091QPilotQ1UPositivityActual
open LeanFormal.IUT.XiFPaper.S1096Q1ULogSupplyActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Canonical qPilot log, filled by the actual qVFam Haar log on qPilotQ1URegion. -/
noncomputable def canonicalQPilotLog : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    (Measure.addHaar : Measure (qVFamTensorBlock T b))
    (qPilotQ1URegion (l := l) T b)

/-- Closed formula for the canonical log, conditional on the exact coefficient gap. -/
theorem s1107CanonicalLogFormula_of_coefficientGap
    (h : S1096CoefficientGap (l := l) T b) :
    canonicalQPilotLog (l := l) T b =
      -((∑ i : qVFamTensorV, qVFamPureCoefficient T b i) *
        Real.log (qVFamTensorP T b : Real)) :=
  s1096Q1ULogFormula_of_coefficientGap (l := l) T b
    (Measure.addHaar : Measure (qVFamTensorBlock T b)) h

/-- Exact minimal input for the closed canonical log formula. -/
def S1107CanonicalLogFormulaExact : Prop :=
  S1096CoefficientGap (l := l) T b

/-- Exact sign/nonvanishing input needed by the qParameter card. -/
def S1107CanonicalLogNonzero : Prop :=
  canonicalQPilotLog (l := l) T b ≠ 0

/-- qParameter card built from the actual canonical log. -/
structure S1107QParameterCard where
  qParameter : Real
  qParameter_eq : qParameter = Real.exp (canonicalQPilotLog (l := l) T b)
  qParameter_pos : 0 < qParameter
  qParameter_log_ne_zero : Real.log qParameter ≠ 0

/-- Actual qParameter card, conditional on nonzero canonical log. -/
noncomputable def s1107QParameterCard
    (h : S1107CanonicalLogNonzero (l := l) T b) :
    S1107QParameterCard (l := l) T b where
  qParameter := Real.exp (canonicalQPilotLog (l := l) T b)
  qParameter_eq := rfl
  qParameter_pos := Real.exp_pos _
  qParameter_log_ne_zero := by
    rw [Real.log_exp]
    exact h

/-- Final checklist: actual canonical log object, exact coefficient gap, exact
nonzero sign, and exact source/finite-link fields. -/
structure S1107FinalChecklist where
  coefficientGap : S1096CoefficientGap (l := l) T b
  canonicalLogNonzero : S1107CanonicalLogNonzero (l := l) T b
  sourceLink : Prop
  linkIdentification : Prop
  finiteLinks : Prop

/-- Concrete checklist constructor: canonical log is actual, card is actual
under the sign field; the remaining link fields are passed unchanged. -/
noncomputable def s1107FinalChecklist
    (hg : S1096CoefficientGap (l := l) T b)
    (hn : S1107CanonicalLogNonzero (l := l) T b)
    (sourceLink linkIdentification finiteLinks : Prop) :
    S1107FinalChecklist (l := l) T b where
  coefficientGap := hg
  canonicalLogNonzero := hn
  sourceLink := sourceLink
  linkIdentification := linkIdentification
  finiteLinks := finiteLinks

end LeanFormal.IUT.XiFPaper.S1107CanonicalQPilotLogActual
end