import tmp.sheaf.xif.paper.BadPlaceNormRatioSourceActual
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.BadPlaceCorrectionSignActual
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
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- The negative factor turning norm-ratio correction into the actual correction. -/
noncomputable def correctionFactor : Real :=
  1 / (2 * l.value : Real) - 1
theorem correctionFactor_neg : correctionFactor (l := l) < 0 := by
  unfold correctionFactor
  have h5 : (5 : Real) ≤ l.value := by exact_mod_cast l.ge_five
  have hden : (2 : Real) ≤ 2 * l.value := by nlinarith
  have hpos : (0 : Real) < 2 * l.value := by linarith
  have hlt : 1 / (2 * l.value : Real) < 1 := by
    rw [div_lt_one hpos]
    linarith
  linarith
/-- Correction is the negative factor times the norm-ratio correction sum. -/
theorem paperNormalizedCorrection_eq_factor_mul :
    paperNormalizedCorrection T =
      correctionFactor (l := l) * normRatioCorrectionSum T := by
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  unfold paperNormalizedCorrection correctionFactor
  have hhalf : halfNormRatioCorrectionSum T =
      normRatioCorrectionSum T / (2 * l.value : Real) := by
    have hmul := twoL_mul_halfNormRatioCorrectionSum T
    rw [eq_div_iff htwo]
    simpa [mul_comm] using hmul
  rw [hhalf]
  ring
/-- Correction is nonpositive exactly when the norm-ratio correction sum is nonnegative. -/
theorem paperNormalizedCorrection_nonpos_iff :
    paperNormalizedCorrection T ≤ 0 ↔ 0 ≤ normRatioCorrectionSum T := by
  rw [paperNormalizedCorrection_eq_factor_mul]
  have hneg := correctionFactor_neg (l := l)
  constructor
  · intro h
    by_contra hc
    have hpos : 0 < -normRatioCorrectionSum T := by linarith
    nlinarith [mul_neg_of_neg_of_pos hneg hpos]
  · intro h
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) h
/-- Correction vanishes exactly when the norm-ratio correction sum vanishes. -/
theorem paperNormalizedCorrection_eq_zero_iff :
    paperNormalizedCorrection T = 0 ↔ normRatioCorrectionSum T = 0 := by
  rw [paperNormalizedCorrection_eq_factor_mul]
  exact mul_eq_zero.trans (or_iff_right (ne_of_lt (correctionFactor_neg (l := l))))
/-- If the paper coefficient equals c_norm at every b, the correction vanishes. -/
theorem paperNormalizedCorrection_eq_zero_of_paper_eq_cNorm
    (h : ∀ b : Bad (nativePlaceSelection T),
      paperNormalizedCoefficient T b =
        QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b) :
    paperNormalizedCorrection T = 0 := by
  rw [paperNormalizedCorrection_eq_zero_iff]
  unfold normRatioCorrectionSum
  apply Finset.sum_eq_zero
  intro b _
  have hratio := (qVFamNormRatio_eq_one_iff_paperCoefficient_eq_cNorm T b).mpr (h b)
  rw [hratio, Real.log_one, mul_zero]
/-- A separated normalization regime: at b the paper coefficient differs from
c_norm, hence qVFamNormRatio is not one. -/
structure SeparatedNormRatioRegime where
  b : Bad (nativePlaceSelection T)
  gap_ne : paperNormalizedCoefficient T b ≠
    QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b
theorem separated_ratio_ne_one (R : SeparatedNormRatioRegime T) :
    qVFamNormRatio T R.b ≠ 1 := by
  intro h
  exact R.gap_ne ((qVFamNormRatio_eq_one_iff_paperCoefficient_eq_cNorm T R.b).mp h)
/-- Regime in which the norm-ratio correction sum is nonzero. -/
structure NonzeroCorrectionRegime where
  sum_ne_zero : normRatioCorrectionSum T ≠ 0

/-- Under the nonzero-correction regime the actual paper-normalized correction
does not vanish; it cannot be silently removed. -/
theorem correction_ne_zero_of_regime
    (R : NonzeroCorrectionRegime T) :
    paperNormalizedCorrection T ≠ 0 := by
  intro h
  exact R.sum_ne_zero ((paperNormalizedCorrection_eq_zero_iff T).mp h)

end LeanFormal.IUT.XiFPaper.BadPlaceCorrectionSignActual
