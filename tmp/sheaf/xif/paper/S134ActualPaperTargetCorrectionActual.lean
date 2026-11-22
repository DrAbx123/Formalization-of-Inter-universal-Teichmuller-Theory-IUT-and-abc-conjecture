import tmp.sheaf.xif.paper.BadPlaceThetaHullScalarBridgeActual
import tmp.sheaf.xif.paper.BadPlaceRationalDegreeActual
import tmp.sheaf.xif.paper.QVFamTensorBlockAlignmentActual
import tmp.sheaf.xif.paper.S121QVFamSpectralValuationActual
import tmp.sheaf.xif.paper.S64DependentThetaHullActual

/-!
# S134: actual paper target up to the norm-ratio correction

The exact Theta-hull correction from S121 is

  qVFamNormRatioCorrection = normRatioCorrectionSum
    = sum_b weight_b * log(qVFamNormRatio_b),

and under the rational-prime log obstruction S121 gives the spectral form

  log(qVFamNormRatio_b)
    = (exponent_b * rationalDegree_b - c_norm_b) * log p_b.

The actual paper target retains the total correction

  totalCorrection
    = normRatioCorrectionSum - halfNormRatioCorrectionSum
      + thetaHullCoefficientCorrection.

It is exactly equivalent to the paper-normalized comparison.  Dropping the
correction is only possible under an extra sign hypothesis; no ratio=1 is
assumed.  No S110 file is present in this workspace, so no S110 bridge is
claimed or contradicted.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S134ActualPaperTargetCorrectionActual

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
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual
open LeanFormal.IUT.XiFPaper.S121QVFamSpectralValuationActual
open LeanFormal.IUT.XiFPaper.S64DependentThetaHullActual
open LeanFormal.IUT.XiFPaper.S92NormRatioUnifiedActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- S121 spectral formula: log norm ratio = (exponent * degree - c_norm) log p. -/
theorem log_normRatio_eq_spectralGap
    (b : Bad (nativePlaceSelection T))
    (hobs : qVFamTensorRationalPrimeLogObstruction T b) :
    Real.log (qVFamNormRatio T b) =
      (((qVFamily T b).exponent : Real) * qVFamTensorRationalDegree T b -
          qVFamNormalizedCoefficient T b) *
        Real.log (qVFamTensorP T b : Real) := by
  have h := qVFamNormalizedCoefficient_eq_exponent_mul_degree_sub_logRatio T hobs
  have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
  have hc : qVFamNormalizedCoefficient T b =
      ((qVFamily T b).exponent : Real) * qVFamTensorRationalDegree T b -
        Real.log (qVFamNormRatio T b) / Real.log (qVFamTensorP T b : Real) := h
  field_simp [hlog] at hc ⊢
  linarith

/-- The S121 spectral form of the q-side correction sum. -/
theorem normRatioCorrectionSum_eq_spectralGapSum
    (hobs : ∀ b : Bad (nativePlaceSelection T),
      qVFamTensorRationalPrimeLogObstruction T b) :
    normRatioCorrectionSum T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((((qVFamily T b).exponent : Real) *
              qVFamTensorRationalDegree T b -
            qVFamNormalizedCoefficient T b) *
            Real.log (qVFamTensorP T b : Real)) := by
  unfold normRatioCorrectionSum
  apply Finset.sum_congr rfl
  intro b _
  rw [log_normRatio_eq_spectralGap T b (hobs b)]

/-- Total actual paper target correction. -/
noncomputable def actualPaperTotalCorrection : Real :=
  normRatioCorrectionSum T - halfNormRatioCorrectionSum T +
    thetaHullCoefficientCorrection T

/-- Actual paper target up to the exact norm-ratio correction. -/
def ActualPaperTargetUpToNormRatioCorrection : Prop :=
  actualThetaHullMagnitudeRoot (l := l) T ≤
    actualQPilotMagnitudeClassical (l := l) T +
      actualPaperTotalCorrection T

/-- The corrected actual target is exactly the paper-normalized comparison. -/
theorem actualPaperTargetUpToNormRatioCorrection_iff_paperComparison :
    ActualPaperTargetUpToNormRatioCorrection T ↔
      paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T := by
  unfold ActualPaperTargetUpToNormRatioCorrection actualPaperTotalCorrection
  exact (paperComparison_iff_actualMagnitude_add_thetaCorrection T).symm

/-- The corrected actual target follows from the paper-normalized comparison. -/
theorem actualPaperTargetUpToNormRatioCorrection_of_paperComparison
    (h : paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T) :
    ActualPaperTargetUpToNormRatioCorrection T :=
  (actualPaperTargetUpToNormRatioCorrection_iff_paperComparison T).mpr h

/-- The corrected actual target is proved from the existing paper-normalized
comparison. -/
theorem actualPaperTargetUpToNormRatioCorrection_direct :
    ActualPaperTargetUpToNormRatioCorrection T :=
  actualPaperTargetUpToNormRatioCorrection_of_paperComparison T
    (paperNormalizedThetaSum_le_qPilotSum_direct T)

/-- The target without the correction. -/
def ActualPaperTargetNoNormRatioCorrection : Prop :=
  actualThetaHullMagnitudeRoot (l := l) T ≤
    actualQPilotMagnitudeClassical (l := l) T

/-- Dropping the correction is valid under the explicit nonpositivity condition. -/
theorem actualPaperTargetNoNormRatioCorrection_of_corrected_and_nonpos
    (h : ActualPaperTargetUpToNormRatioCorrection T)
    (hcorr : actualPaperTotalCorrection T ≤ 0) :
    ActualPaperTargetNoNormRatioCorrection T := by
  unfold ActualPaperTargetUpToNormRatioCorrection at h
  unfold ActualPaperTargetNoNormRatioCorrection
  linarith

/-- If the total correction is zero, the corrected target and the uncorrected
target are equivalent. -/
theorem actualPaperTargetNoNormRatioCorrection_iff_of_correction_zero
    (hcorr : actualPaperTotalCorrection T = 0) :
    ActualPaperTargetUpToNormRatioCorrection T ↔
      ActualPaperTargetNoNormRatioCorrection T := by
  unfold ActualPaperTargetUpToNormRatioCorrection
    ActualPaperTargetNoNormRatioCorrection
  rw [hcorr, add_zero]

end LeanFormal.IUT.XiFPaper.S134ActualPaperTargetCorrectionActual

end
