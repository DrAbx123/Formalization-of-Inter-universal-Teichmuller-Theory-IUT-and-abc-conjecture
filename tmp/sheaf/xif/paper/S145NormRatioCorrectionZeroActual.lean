import tmp.sheaf.xif.paper.S137PaperTargetCorrectionStatusActual
import tmp.sheaf.xif.paper.S134ActualPaperTargetCorrectionActual
import tmp.sheaf.xif.paper.BadPlaceRationalDegreeActual
import tmp.sheaf.xif.paper.QVFamTensorBlockAlignmentActual

/-!
# S145: zero and nonzero regimes for the norm-ratio correction

The correction is

  normRatioCorrectionSum = sum_b weight_b * log(qVFamNormRatio_b).

Under the rational-prime log obstruction S121 gives

  log(qVFamNormRatio_b) = (exponent_b * rationalDegree_b - c_norm_b) * log p_b.

Therefore nonnegative spectral gaps with at least one positive gap and positive
weights give a strictly positive correction; nonpositive gaps with one negative
gap give a strictly negative correction.  This is an actual nonzero regime.
The zero case is exactly the weighted spectral-gap zero condition.

No unconditional zero and no fake ratio=1.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S145NormRatioCorrectionZeroActual

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
open LeanFormal.IUT.XiFPaper.S134ActualPaperTargetCorrectionActual
open LeanFormal.IUT.XiFPaper.S137PaperTargetCorrectionStatusActual
open LeanFormal.IUT.XiFPaper.S92NormRatioUnifiedActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Actual spectral gap at a bad place. -/
noncomputable def normRatioSpectralGap
    (b : Bad (nativePlaceSelection T)) : Real :=
  (((qVFamily T b).exponent : Real) * qVFamTensorRationalDegree T b -
      qVFamNormalizedCoefficient T b) *
    Real.log (qVFamTensorP T b : Real)

/-- The correction is the weighted sum of spectral gaps. -/
theorem normRatioCorrectionSum_eq_weighted_spectralGap
    (hobs : ∀ b : Bad (nativePlaceSelection T),
      qVFamTensorRationalPrimeLogObstruction T b) :
    normRatioCorrectionSum T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * normRatioSpectralGap T b := by
  unfold normRatioSpectralGap
  rw [normRatioCorrectionSum_eq_spectralGapSum T hobs]

/-- Actual positive regime: nonnegative spectral gaps, one positive gap and
positive weights imply a strictly positive correction. -/
theorem normRatioCorrectionSum_pos_of_spectralGap
    (hobs : ∀ b : Bad (nativePlaceSelection T),
      qVFamTensorRationalPrimeLogObstruction T b)
    (hweight : ∀ b : Bad (nativePlaceSelection T),
      0 < nativeBadLocalWeight T b)
    (hgap_nonneg : ∀ b : Bad (nativePlaceSelection T),
      0 ≤ normRatioSpectralGap T b)
    (hgap_pos : ∃ b : Bad (nativePlaceSelection T),
      0 < normRatioSpectralGap T b) :
    0 < normRatioCorrectionSum T := by
  rw [normRatioCorrectionSum_eq_weighted_spectralGap T hobs]
  rcases hgap_pos with ⟨b0, hb0⟩
  apply Finset.sum_pos'
  · intro b _
    exact mul_nonneg (le_of_lt (hweight b)) (hgap_nonneg b)
  · exact ⟨b0, Finset.mem_univ b0,
      mul_pos (hweight b0) hb0⟩

/-- Actual negative regime: nonpositive spectral gaps, one negative gap and
positive weights imply a strictly negative correction. -/
theorem normRatioCorrectionSum_neg_of_spectralGap
    (hobs : ∀ b : Bad (nativePlaceSelection T),
      qVFamTensorRationalPrimeLogObstruction T b)
    (hweight : ∀ b : Bad (nativePlaceSelection T),
      0 < nativeBadLocalWeight T b)
    (hgap_nonpos : ∀ b : Bad (nativePlaceSelection T),
      normRatioSpectralGap T b ≤ 0)
    (hgap_neg : ∃ b : Bad (nativePlaceSelection T),
      normRatioSpectralGap T b < 0) :
    normRatioCorrectionSum T < 0 := by
  rw [normRatioCorrectionSum_eq_weighted_spectralGap T hobs]
  rcases hgap_neg with ⟨b0, hb0⟩
  apply Finset.sum_neg'
  · intro b _
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hweight b)) (hgap_nonpos b)
  · exact ⟨b0, Finset.mem_univ b0,
      mul_neg_of_pos_of_neg (hweight b0) hb0⟩

/-- Zero correction in the spectral-gap form. -/
theorem normRatioCorrectionSum_eq_zero_of_spectralGap_zero
    (hobs : ∀ b : Bad (nativePlaceSelection T),
      qVFamTensorRationalPrimeLogObstruction T b)
    (hgap : ∀ b : Bad (nativePlaceSelection T),
      normRatioSpectralGap T b = 0) :
    normRatioCorrectionSum T = 0 := by
  rw [normRatioCorrectionSum_eq_weighted_spectralGap T hobs]
  apply Finset.sum_eq_zero
  intro b _
  rw [hgap b, mul_zero]

/-- A nonzero spectral gap gives a nonzero log norm ratio at that place. -/
theorem log_qVFamNormRatio_ne_zero_of_spectralGap_ne_zero
    (hobs : qVFamTensorRationalPrimeLogObstruction T b)
    (hgap : normRatioSpectralGap T b ≠ 0) :
    Real.log (qVFamNormRatio T b) ≠ 0 := by
  intro hlog
  have hformula := log_normRatio_eq_spectralGap T b hobs
  unfold normRatioSpectralGap at hgap
  apply hgap
  rw [← hformula]
  exact hlog

/-- If the correction is zero, the intermediate corrected target and the
uncorrected actual target are equivalent. -/
theorem intermediateTarget_iff_uncorrected_of_normRatioCorrectionZero
    (hzero : normRatioCorrectionSum T = 0)
    (hhalfzero : halfNormRatioCorrectionSum T = 0)
    (hthetazero : thetaHullCoefficientCorrection T = 0) :
    IntermediateActualPaperTargetUpToNormRatioCorrection T ↔
      ActualPaperTargetNoNormRatioCorrection T := by
  have hcorr : actualPaperTotalCorrection T = 0 := by
    unfold actualPaperTotalCorrection
    rw [hzero, hhalfzero, hthetazero]
    ring
  exact intermediateTarget_iff_uncorrected_of_correction_zero T hcorr

end LeanFormal.IUT.XiFPaper.S145NormRatioCorrectionZeroActual

end
