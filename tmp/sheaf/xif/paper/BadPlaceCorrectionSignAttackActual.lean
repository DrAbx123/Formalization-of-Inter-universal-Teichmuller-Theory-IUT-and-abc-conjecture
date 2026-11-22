import tmp.sheaf.xif.paper.BadPlaceCorrectionSignActual

/-! # Attacking the correction sign and exact paper-normalized comparison

The norm-ratio correction has sign opposite to normRatioCorrectionSum because
the factor is 1/(2l)-1 < 0.  This file proves the two per-b sign regimes
(ratio <= 1 and ratio >= 1) and their weighted-sum consequences.  It also
proves the exact paper-normalized comparison directly from the positivity of
paperNormalizedCoefficient and the 1/(2l) root factor; this does not require
ratio = 1.

No fake ratio inequality. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceCorrectionSignAttackActual

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
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeActual
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeFactorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioSourceActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizedSourceHypothesisActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionSignActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Paper-normalized coefficient is nonnegative. -/
theorem paperNormalizedCoefficient_nonneg :
    0 ≤ paperNormalizedCoefficient T b := by
  unfold paperNormalizedCoefficient
  have hlogR : 0 ≤ Real.log (residueNormBase (qVFamTensorPlace T b)) :=
    le_of_lt (log_residueNormBase_pos (qVFamTensorPlace T b))
  have hlogp : 0 < Real.log (qVFamTensorP T b : Real) := by
    apply Real.log_pos
    have hp : Nat.Prime (qVFamTensorP T b) := Fact.out
    exact_mod_cast hp.one_lt
  have horder : 0 ≤ ((qVFamily T b).order : Real) := by positivity
  exact mul_nonneg horder (div_nonneg hlogR (le_of_lt hlogp))

/-- Exact paper-normalized comparison, direct from coefficient positivity and
the 1/(2l) root factor. -/
theorem paperNormalizedThetaSum_le_qPilotSum_direct :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T := by
  unfold paperNormalizedThetaSum paperNormalizedQPilotSum
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left ?_ (badPlaceNativeBadLocalWeight_nonneg T b)
  apply mul_le_mul_of_nonneg_right ?_ ?_
  · have hc := paperNormalizedCoefficient_nonneg T b
    have hden : (1 : Real) ≤ 2 * (l.value : Real) := by
      have h5 : (5 : Real) ≤ l.value := by exact_mod_cast l.ge_five
      nlinarith
    exact div_le_self hc hden
  · apply Real.log_nonneg
    have hp : Nat.Prime (qVFamTensorP T b) := Fact.out
    exact_mod_cast hp.one_le

/-- Per-b ratio <= 1 implies log ratio <= 0. -/
theorem log_qVFamNormRatio_nonpos_of_le_one
    (h : qVFamNormRatio T b ≤ 1) :
    Real.log (qVFamNormRatio T b) ≤ 0 :=
  Real.log_nonpos (le_of_lt (qVFamNormRatio_pos T b)) h

/-- If every ratio is <= 1, the weighted norm-ratio correction sum is <= 0. -/
theorem normRatioCorrectionSum_nonpos_of_ratio_le_one
    (h : ∀ b : Bad (nativePlaceSelection T), qVFamNormRatio T b ≤ 1) :
    normRatioCorrectionSum T ≤ 0 := by
  unfold normRatioCorrectionSum
  apply Finset.sum_nonpos
  intro b _
  exact mul_nonpos_of_nonneg_of_nonpos (badPlaceNativeBadLocalWeight_nonneg T b)
    (log_qVFamNormRatio_nonpos_of_le_one T b (h b))

/-- In the ratio <= 1 regime the actual correction is nonnegative. -/
theorem paperNormalizedCorrection_nonneg_of_ratio_le_one
    (h : ∀ b : Bad (nativePlaceSelection T), qVFamNormRatio T b ≤ 1) :
    0 ≤ paperNormalizedCorrection T := by
  rw [paperNormalizedCorrection_eq_factor_mul]
  exact mul_nonneg_of_nonpos_of_nonpos
    (le_of_lt (correctionFactor_neg (l := l)))
    (normRatioCorrectionSum_nonpos_of_ratio_le_one T h)

/-- If every ratio is >= 1, the weighted norm-ratio correction sum is >= 0. -/
theorem normRatioCorrectionSum_nonneg_of_one_le_ratio
    (h : ∀ b : Bad (nativePlaceSelection T), 1 ≤ qVFamNormRatio T b) :
    0 ≤ normRatioCorrectionSum T := by
  unfold normRatioCorrectionSum
  apply Finset.sum_nonneg
  intro b _
  apply mul_nonneg (badPlaceNativeBadLocalWeight_nonneg T b)
  exact Real.log_nonneg (by linarith [le_of_lt (qVFamNormRatio_pos T b), h b])

/-- In the ratio >= 1 regime the actual correction is nonpositive, hence the
exact paper-normalized comparison follows. -/
theorem paperNormalizedComparison_exact_of_ratio_ge_one
    (h : ∀ b : Bad (nativePlaceSelection T), 1 ≤ qVFamNormRatio T b) :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T := by
  have hsum := normRatioCorrectionSum_nonneg_of_one_le_ratio T h
  have hcorr : paperNormalizedCorrection T ≤ 0 := by
    rw [paperNormalizedCorrection_eq_factor_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (correctionFactor_neg (l := l))) hsum
  exact paperNormalizedComparison_exact_of_correction_nonpos T hcorr

end LeanFormal.IUT.XiFPaper.BadPlaceCorrectionSignAttackActual
