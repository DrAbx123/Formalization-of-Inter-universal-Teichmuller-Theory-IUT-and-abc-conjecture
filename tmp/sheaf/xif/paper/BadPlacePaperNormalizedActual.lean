import tmp.sheaf.xif.paper.BadPlaceNormRatioCorrectionActual

/-! # Actual paper-normalized final comparison

This packages the S84 result: the final comparison is exactly

  paperNormalizedTheta <= paperNormalizedQPilot + actualCorrection,

with actualCorrection = halfNormRatioCorrection - normRatioCorrection, and the
correction bounded by the actual norm-ratio coefficient gap.  The rational
degree is already inside paperNormalizedCoefficient, so no degree correction is
introduced.

qVFamNormRatio = 1 is not proved from source normalization; the exact source
condition is kept separately.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedActual

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
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizedSourceHypothesisActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual correction term in the paper-normalized comparison. -/
noncomputable def paperNormalizedCorrection : Real :=
  halfNormRatioCorrectionSum T - normRatioCorrectionSum T

/-- The per-b coefficient gap bound for the norm-ratio correction. -/
noncomputable def normRatioGapBound : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (|paperNormalizedCoefficient T b -
          QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b| *
        |Real.log (qVFamTensorP T b : Real)|)

/-- S13's coefficient comparison follows from c_norm >= 0 and the 1/(2l) root
factor. -/
theorem s13ThetaCoefficientSum_le_qPilot :
    s13ThetaCoefficientSum T ≤ s13QPilotCoefficientSum T := by
  unfold s13ThetaCoefficientSum s13QPilotCoefficientSum
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left ?_ (badPlaceNativeBadLocalWeight_nonneg T b)
  apply mul_le_mul_of_nonneg_right ?_ ?_
  · have hc : 0 ≤ QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b :=
      qVFamNormalizedCoefficient_nonneg T b
    have hden : (1 : Real) ≤ 2 * (l.value : Real) := by
      have h5 : (5 : Real) ≤ l.value := by exact_mod_cast l.ge_five
      nlinarith
    exact div_le_self hc hden
  · apply Real.log_nonneg
    have hp2 : (1 : Real) ≤ (qVFamTensorP T b : Real) := by
      have hp : Nat.Prime (qVFamTensorP T b) := Fact.out
      exact_mod_cast hp.one_le
    exact hp2

/-- The actual paper-normalized comparison with correction. -/
theorem paperNormalizedComparison_with_correction :
    paperNormalizedThetaSum T ≤
      paperNormalizedQPilotSum T + paperNormalizedCorrection T :=
  (s13Comparison_iff_paperNormalized_add_normRatio T).mp
    (s13ThetaCoefficientSum_le_qPilot T)

/-- The correction is half of the norm-ratio correction minus itself. -/
theorem paperNormalizedCorrection_eq :
    paperNormalizedCorrection T =
      halfNormRatioCorrectionSum T - normRatioCorrectionSum T := rfl

/-- The correction bound by the actual norm-ratio coefficient gap. -/
theorem abs_paperNormalizedCorrection_le_gap :
    |paperNormalizedCorrection T| ≤ normRatioGapBound T := by
  rw [paperNormalizedCorrection_eq]
  -- half = norm/(2l), so correction = norm * (1/(2l) - 1)
  have hhalf : halfNormRatioCorrectionSum T =
      normRatioCorrectionSum T / (2 * l.value : Real) := by
    have htwo : (2 * l.value : Real) ≠ 0 := by
      exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
    have hmul := twoL_mul_halfNormRatioCorrectionSum T
    rw [eq_div_iff htwo]
    simpa [mul_comm] using hmul
  rw [hhalf]
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  have hfac_nonneg : 0 ≤ 1 / (2 * l.value : Real) :=
    div_nonneg zero_le_one (by positivity)
  have hfac_le_one : 1 / (2 * l.value : Real) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have hden : (1 : Real) ≤ 2 * (l.value : Real) := by
      have h5 : (5 : Real) ≤ l.value := by exact_mod_cast l.ge_five
      nlinarith
    exact hden
  have hfac_abs : |1 / (2 * l.value : Real) - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  calc
    |normRatioCorrectionSum T / (2 * l.value : Real) - normRatioCorrectionSum T|
        = |normRatioCorrectionSum T * (1 / (2 * l.value : Real) - 1)| := by ring_nf
    _ = |normRatioCorrectionSum T| * |1 / (2 * l.value : Real) - 1| := abs_mul _ _
    _ ≤ |normRatioCorrectionSum T| * 1 := by
      exact mul_le_mul_of_nonneg_left hfac_abs (abs_nonneg _)
    _ = |normRatioCorrectionSum T| := mul_one _
    _ ≤ normRatioGapBound T := abs_normRatioCorrectionSum_le T

/-- Exact source condition under which the correction vanishes. -/
def NormRatioOneSourceCondition : Prop :=
  ∀ b : Bad (nativePlaceSelection T), qVFamNormRatio T b = 1

/-- Under the exact source condition the paper-normalized comparison has zero
correction. -/
theorem paperNormalizedComparison_exact_of_normRatio_one
    (h : NormRatioOneSourceCondition T) :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T := by
  have hzero : paperNormalizedCorrection T = 0 := by
    unfold paperNormalizedCorrection
    have hnorm : normRatioCorrectionSum T = 0 := by
      unfold normRatioCorrectionSum
      apply Finset.sum_eq_zero
      intro b _
      rw [h b, Real.log_one, mul_zero]
    have hhalf : halfNormRatioCorrectionSum T = 0 := by
      have htwo : (2 * l.value : Real) ≠ 0 := by
        exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
      have hmul : (2 * l.value : Real) * halfNormRatioCorrectionSum T = 0 := by
        rw [twoL_mul_halfNormRatioCorrectionSum T, hnorm]
      exact (mul_eq_zero.mp hmul).resolve_left htwo
    rw [hhalf, hnorm, sub_self]
  simpa [hzero] using paperNormalizedComparison_with_correction T

/-- Actual packaged paper-normalized comparison. -/
structure PaperNormalizedComparisonActual where
  theta : Real
  theta_eq : theta = paperNormalizedThetaSum T
  qPilot : Real
  qPilot_eq : qPilot = paperNormalizedQPilotSum T
  correction : Real
  correction_eq : correction = paperNormalizedCorrection T
  comparison : theta ≤ qPilot + correction
  correction_bound : |correction| ≤ normRatioGapBound T

/-- The actual packaged paper-normalized comparison, with actual correction
bound. -/
noncomputable def paperNormalizedComparisonActual :
    PaperNormalizedComparisonActual T where
  theta := paperNormalizedThetaSum T
  theta_eq := rfl
  qPilot := paperNormalizedQPilotSum T
  qPilot_eq := rfl
  correction := paperNormalizedCorrection T
  correction_eq := rfl
  comparison := paperNormalizedComparison_with_correction T
  correction_bound := abs_paperNormalizedCorrection_le_gap T

end LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedActual
