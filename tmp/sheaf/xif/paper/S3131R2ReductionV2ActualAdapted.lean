import tmp.sheaf.xif.paper.S3131CoefficientReductionActual
import tmp.sheaf.xif.paper.S3131QCLeHCComparisonActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual

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

namespace LeanFormal.IUT.XiFPaper.S3131R2ReductionV2ActualAdapted

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
open LeanFormal.IUT.IUTII.Frobenioid.Example36
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

/-- **(iii-b) PROVED.**  Valuation exponent of the normalized generator equals
the actual qVFamily discrete exponent. -/
theorem S3131Nu_qVFamNormalizedGenerator_eq_exponent :
    completionValuationExponent (qVFamTensorPlace T b).maximalIdeal
      (Units.mk0 (qVFamNormalizedGenerator T b)
        (qVFamNormalizedGenerator_ne_zero T b))
      = (qVFamily T b).exponent := by
  rw [completionValuationExponent_eq_neg_log]
  have hq : Valued.v ((qVFamily T b).q :
      Completion (qVFamTensorPlace T b)) ≠ 0 :=
    (qVFamily T b).valuation_ne_zero
  have hval : ((qVFamNormalizedGenerator T b :
      NormalizedCompletion (qVFamTensorPlace T b)))
      = ((qVFamily T b).q : Completion (qVFamTensorPlace T b)) :=
    rfl
  rw [hval]
  unfold FinitePlaceQCandidate.exponent
  congr 1
  have h1 : WithZero.exp (Multiplicative.toAdd (WithZero.unzero hq)) =
      Valued.v ((qVFamily T b).q : Completion (qVFamTensorPlace T b)) := by
    unfold WithZero.exp
    rw [Multiplicative.ofAdd_toAdd, WithZero.coe_unzero hq]
  rw [← h1, WithZero.log_exp]

/-- **(iii-a) tree-specific half CLOSED.** -/
theorem S3131QVFamTensorP_eq_natGenerator :
    qVFamTensorP T b =
      Rat.HeightOneSpectrum.natGenerator
        ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal) := rfl

/-- **(iii-a) EXACT RESIDUAL.** -/
def S3131RationalPlaceAbsNormMissing : Prop :=
  (Ideal.absNorm (comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.asIdeal
    : ℝ) = (qVFamTensorP T b : ℝ)

/-- **(iii-a) REDUCTION to the single Mathlib identity.** -/
theorem S3131RationalPlaceAbsNorm_reduction :
    S3131RationalPlaceAbsNormMissing T b ↔
      Ideal.absNorm (comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.asIdeal
        = Rat.HeightOneSpectrum.natGenerator
          ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal) := by
  unfold S3131RationalPlaceAbsNormMissing
  rw [S3131QVFamTensorP_eq_natGenerator]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

#check S3131Nu_qVFamNormalizedGenerator_eq_exponent
#check S3131QVFamTensorP_eq_natGenerator
#check S3131RationalPlaceAbsNorm_reduction

end LeanFormal.IUT.XiFPaper.S3131R2ReductionV2ActualAdapted

end