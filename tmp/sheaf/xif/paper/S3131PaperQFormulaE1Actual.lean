import tmp.sheaf.xif.paper.S3131CoefficientReductionActual
import tmp.sheaf.xif.paper.S3131QCLeHCComparisonActual

/-! # S3131: canonical Batch-A/4th-triangle Q_C, H_C (paper-faithful rooted spectral)

Paper normalization is Q_p-spectral (c_norm = order/e; IUT III Rem 3.1.1(ii),
Prop 3.9(i); IUT IV Prop 1.4(i)).  Canonical q-side readout = Remark 3.1.1(ii)
weighted procession-normalized log-volume of the paper-faithful ROOTED SPECTRAL
q-pilot region qPilotPaperRegion (coefficient rootHalfCoefficient = c_norm/(2l)).
By construction this IS -|log q| in the paper normalization (sign convention);
no e=1 hypothesis.  H_C = same weights * rootThetaHullLog at rootHalf.
The old default-residue readout S3131QC and QVFamNormalizedCoefficientGap are a
separate optional identification; IUT main application F = Q gives e = 1
automatically so conventions coincide (S3131PaperRootCoefficient_eq_ramification_mul_rootHalf).
No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3131PaperQFormulaE1Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.S826CNormOrderRamificationActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S778PaperQPilotHalfRegionActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S918RQpilotVolumeLeSHullActual
open LeanFormal.IUT.XiFPaper.S929RQpilotPaperSHullFinalActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3131HullActualReadout
open LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual
open LeanFormal.IUT.XiFPaper.S3131CoefficientReductionActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- **task-49 (main-application e=1): coefficients coincide.**  At e = 1 the
tree paper root coefficient order/(2l) equals the paper-faithful rooted spectral
coefficient c_norm/(2l). -/
theorem S3131PaperRootCoefficient_eq_rootHalf_of_e_one
    (hcomp : QVFamNormalizedNormCompatibility T b 1) :
    qVFamPaperRootCoefficient T b = rootHalfCoefficient T b () := by
  have h := S3131PaperRootCoefficient_eq_ramification_mul_rootHalf
    (l := l) T b 1 (by norm_num) hcomp
  rw [h, one_mul]

/-- **task-49 reduction (general e).**  The S778 per-b formula is equivalent to
the existence of an actual normalized-root generator supply at the rooted
spectral coefficient. -/
theorem S3131PaperQFormula_iff_scalingData :
    PaperQPilotLogFormulaIdentification (l := l) T b mu ↔
      Nonempty (ArithmeticTuplePureFractionalScalingData
        (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootHalfCoefficient (l := l) T b)) := by
  constructor
  · intro _
    exact ⟨qVFamNormalizedPureFractionalScalingData (l := l) T b⟩
  · intro ⟨data⟩
    unfold PaperQPilotLogFormulaIdentification
    simpa [qPilotPaperLog] using
      qPilotClassicalLog_eq (qVFamTensorPlaces T b) qVFamTensorTuple
        (mu b) (rootHalfCoefficient (l := l) T b) data

#check S3131PaperRootCoefficient_eq_rootHalf_of_e_one
#check S3131PaperQFormula_iff_scalingData

end LeanFormal.IUT.XiFPaper.S3131PaperQFormulaE1Actual

end