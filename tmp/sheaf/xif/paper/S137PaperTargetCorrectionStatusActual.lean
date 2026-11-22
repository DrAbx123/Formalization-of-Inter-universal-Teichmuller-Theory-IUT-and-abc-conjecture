import tmp.sheaf.xif.paper.S134ActualPaperTargetCorrectionActual
import tmp.sheaf.xif.paper.S100QVFamNormInstanceGapActual
import tmp.sheaf.xif.paper.BadPlaceRationalDegreeActual
import tmp.sheaf.xif.paper.QVFamTensorBlockAlignmentActual

/-!
# S137: status of the corrected target

The corrected actual-paper target from S134 is an INTERMEDIATE target.  It is
exactly equivalent to the paper-normalized comparison, but it is not the paper
target unless the total correction is nonpositive.  The uncorrected actual
target remains the paper target.

The norm-ratio correction is still not proved zero.  This file records the
exact zero criterion, the S121 spectral-gap criterion, and a formal separation:
for positive correction the corrected inequality does not imply the
uncorrected one.  No ratio=1 is assumed.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S137PaperTargetCorrectionStatusActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizationSourceActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootComparisonActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionControlActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioSourceActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionSignActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionSignAttackActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedTargetBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlaceThetaHullScalarBridgeActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S121QVFamSpectralValuationActual
open LeanFormal.IUT.XiFPaper.S134ActualPaperTargetCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual
open LeanFormal.IUT.XiFPaper.S100QVFamNormInstanceGapActual
open LeanFormal.IUT.XiFPaper.S92NormRatioUnifiedActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The S134 corrected target is explicitly intermediate. -/
def IntermediateActualPaperTargetUpToNormRatioCorrection : Prop :=
  ActualPaperTargetUpToNormRatioCorrection T

/-- The intermediate corrected target is exactly the paper-normalized
comparison, not the uncorrected paper target. -/
theorem intermediateTarget_iff_paperComparison :
    IntermediateActualPaperTargetUpToNormRatioCorrection T ↔
      paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T := by
  unfold IntermediateActualPaperTargetUpToNormRatioCorrection
  exact actualPaperTargetUpToNormRatioCorrection_iff_paperComparison T

/-- If the total correction is nonpositive, the corrected intermediate target
implies the uncorrected actual target (not conversely). -/
theorem actualPaperTargetNoNormRatioCorrection_of_intermediateTarget_of_correction_nonpos
    (h : IntermediateActualPaperTargetUpToNormRatioCorrection T)
    (hcorr : actualPaperTotalCorrection T ≤ 0) :
    ActualPaperTargetNoNormRatioCorrection T := by
  unfold IntermediateActualPaperTargetUpToNormRatioCorrection
    ActualPaperTargetUpToNormRatioCorrection at h
  unfold ActualPaperTargetNoNormRatioCorrection
  linarith

/-- If the correction is zero, intermediate and uncorrected targets coincide. -/
theorem intermediateTarget_iff_uncorrected_of_correction_zero
    (hcorr : actualPaperTotalCorrection T = 0) :
    IntermediateActualPaperTargetUpToNormRatioCorrection T ↔
      ActualPaperTargetNoNormRatioCorrection T := by
  unfold IntermediateActualPaperTargetUpToNormRatioCorrection
    ActualPaperTargetUpToNormRatioCorrection
    ActualPaperTargetNoNormRatioCorrection
  rw [hcorr, add_zero]

/-- The uncorrected paper target implies the corrected intermediate target when
the correction is nonnegative. -/
theorem intermediateTarget_of_uncorrected_of_correction_nonneg
    (h : ActualPaperTargetNoNormRatioCorrection T)
    (hcorr : 0 ≤ actualPaperTotalCorrection T) :
    IntermediateActualPaperTargetUpToNormRatioCorrection T := by
  unfold IntermediateActualPaperTargetUpToNormRatioCorrection
    ActualPaperTargetUpToNormRatioCorrection
    ActualPaperTargetNoNormRatioCorrection at *
  linarith

/-- Formal separation: for a positive correction, the corrected inequality is
strictly weaker than the uncorrected one.  This is the reason the corrected form
is only an intermediate target. -/
theorem correctedInequality_not_implying_uncorrected_of_correction_pos
    (hcorr : 0 < actualPaperTotalCorrection T) :
    ¬ (∀ A Q : Real,
        A ≤ Q + actualPaperTotalCorrection T → A ≤ Q) := by
  intro h
  have hbad : (actualPaperTotalCorrection T / 2) ≤
      0 + actualPaperTotalCorrection T := by linarith
  have hle : (actualPaperTotalCorrection T / 2) ≤ (0 : Real) :=
    h (actualPaperTotalCorrection T / 2) 0 hbad
  linarith

/-- Exact zero criterion for the q-side norm-ratio correction: weighted log
ratio sum zero. -/
theorem normRatioCorrectionSum_eq_zero_iff_weighted_log_zero :
    normRatioCorrectionSum T = 0 ↔
      (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * Real.log (qVFamNormRatio T b)) = 0 :=
  Iff.rfl

/-- S121 spectral-gap form of the same zero criterion. -/
theorem normRatioCorrectionSum_eq_zero_iff_spectralGapSum_zero
    (hobs : ∀ b : Bad (nativePlaceSelection T),
      qVFamTensorRationalPrimeLogObstruction T b) :
    normRatioCorrectionSum T = 0 ↔
      (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((((qVFamily T b).exponent : Real) *
              qVFamTensorRationalDegree T b -
            qVFamNormalizedCoefficient T b) *
            Real.log (qVFamTensorP T b : Real))) = 0 := by
  rw [normRatioCorrectionSum_eq_spectralGapSum T hobs]

/-- The correction is zero whenever the paper-normalized coefficient equals
c_norm at every bad place. -/
theorem normRatioCorrectionSum_eq_zero_of_coefficient_eq
    (h : ∀ b : Bad (nativePlaceSelection T),
      paperNormalizedCoefficient T b = qVFamNormalizedCoefficient T b) :
    normRatioCorrectionSum T = 0 :=
  S92NormRatioUnifiedActual.normRatioCorrectionSum_eq_zero_of_coefficient_eq (T := T) h

end LeanFormal.IUT.XiFPaper.S137PaperTargetCorrectionStatusActual

end
