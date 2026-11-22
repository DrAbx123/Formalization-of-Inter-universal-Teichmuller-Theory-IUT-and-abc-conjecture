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

namespace LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
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
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- Canonical Q_C: paper-faithful rooted spectral q-pilot procession readout. -/
noncomputable def S3131CanonicalRootedQC : ℝ :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * qPilotPaperLog (l := l) T b (mu b)

/-- Canonical H_C: paper-faithful rooted spectral Theta-hull readout. -/
noncomputable def S3131CanonicalRootedHC : ℝ :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (mu b) (rootHalfCoefficient (l := l) T b)

/-- Signed 4th-triangle comparison in the paper normalization, UNCONDITIONAL. -/
theorem S3131CanonicalRootedQC_le_HC :
    S3131CanonicalRootedQC (l := l) T mu ≤ S3131CanonicalRootedHC (l := l) T mu :=
  S3131PaperFaithfulRegionalRootedComparison (l := l) T mu

/-- Magnitude form: |log Theta| <= |log q|. -/
theorem S3131CanonicalRootedMagnitude :
    -S3131CanonicalRootedHC (l := l) T mu ≤ -S3131CanonicalRootedQC (l := l) T mu := by
  linarith [S3131CanonicalRootedQC_le_HC (l := l) T mu]

#check S3131CanonicalRootedQC
#check S3131CanonicalRootedHC
#check S3131CanonicalRootedQC_le_HC
#check S3131CanonicalRootedMagnitude

end LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual

end
