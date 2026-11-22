import tmp.sheaf.xif.paper.S3134MainlineRootedHFaActual

/-!
# S3134 task-35: honesty record for the canonical q readout (S778 formula gap)

**Component, not paper object.**  The canonical q-side readout
`S3131CanonicalRootedQC` (mainline, landed) is *defined* as the paper-normalized
q-pilot readout: it is the weighted signed log-volume of the paper-faithful
rooted spectral q-pilot region `qPilotPaperLog` at `rootHalfCoefficient`.  In the
paper's Q_p-spectral normalization, `-|log q|` is the paper's notation for this
quantity (IUT III, Remark 3.1.1(ii); Prop. 3.9(i) p. 115; IUT IV, Prop. 1.4(i)).

There is NO separate scalar theorem `S3131CanonicalRootedQC = -|log q|`.
Obtaining an explicit scalar value requires the registered per-b S778
identification

  `PaperQPilotLogFormulaIdentification`:
    `qPilotPaperLog_b = -(sum_i rootHalfCoefficient_{b,i}) * log p_b`

(S778PaperQPilotHalfRegionActual, ~line 112), which is NOT proved.  We record
this here as `S3134CanonicalQFormulaGap` and prove the only honest numeric form:
granting the gap, the canonical readout has the explicit scalar expression.
The *comparison* does not depend on the gap (it is mainline's unconditional
paper-faithful rooted comparison).

No numeric equality is claimed without the gap.  WRITE-ONLY: no lake/lean.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S778PaperQPilotHalfRegionActual
open LeanFormal.IUT.XiFPaper.S3131CoefficientReductionActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3134CanonicalQFormulaGapActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- The explicit-scalar q residual: the registered per-b S778 formula
identification `qPilotPaperLog_b = -(sum_i rootHalfCoefficient_i) * log p_b`.
NOT proved; it is the only gap between the canonical (convention-defined) paper q
readout and an explicit scalar `-|log q|`. -/
def S3134CanonicalQFormulaGap : Prop :=
  S3134CanonicalRootedQFormulaGap (l := l) T mu

/-- Honest numeric form: only under the S778 formula gap does the canonical
Q_C readout have an explicit scalar expression. -/
theorem S3134CanonicalQFormulaGap_scalar
    (h : S3134CanonicalQFormulaGap (l := l) T mu) :
    S3134CanonicalRootedQC (l := l) T mu =
      -∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((∑ i, rootHalfCoefficient (l := l) T b i) *
            Real.log (qVFamTensorP T b : ℝ)) :=
  S3134CanonicalRootedQC_eq_scalar_of_formulaGap (l := l) T mu h

/-- The canonical (paper-faithful rooted) comparison does NOT depend on the
S778 formula gap: it is mainline's unconditional theorem. -/
theorem S3134CanonicalComparison_independent_ofFormulaGap :
    S3134CanonicalRootedQC (l := l) T mu ≤
      S3134CanonicalRootedHC (l := l) T mu :=
  S3134CanonicalRootedQC_le_HC (l := l) T mu

#check S3134CanonicalQFormulaGap
#check S3134CanonicalQFormulaGap_scalar
#check S3134CanonicalComparison_independent_ofFormulaGap

end LeanFormal.IUT.XiFPaper.S3134CanonicalQFormulaGapActual
