import tmp.sheaf.xif.paper.BadPlacePaperRootComparisonActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-! # Exact control of the qVFamily normalization correction

Using the actual source identity

  correction_b * log p_b =
    order_b * (log(residueNormBase F-place) - log p_b) - log(qVFamNormRatio_b),

this file computes the weighted q-side correction sum exactly, proves it
vanishes under the actual normalized-source condition, and gives an actual
absolute-value correction bound in the nonzero case.  The final S13 weighted
comparison is restated as the paper-root comparison plus the correction term,
with no assumption correction = 0.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceCorrectionControlActual

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
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Exact value of the q-side correction sum in terms of the actual source
normalization data. -/
theorem qCorrectionSum_eq_sourceTerm :
    qCorrectionSum T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((qVFamily T b).order *
              (Real.log (residueNormBase (qVFamTensorPlace T b)) -
                Real.log (qVFamTensorP T b : Real)) -
            Real.log (qVFamNormRatio T b)) := by
  unfold qCorrectionSum
  apply Finset.sum_congr rfl
  intro b _
  have h := qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio T b
  unfold normalizedOrderCorrection
  rw [sub_mul, h]
  ring

/-- If every correction vanishes, the weighted q-side correction sum is zero. -/
theorem qCorrectionSum_eq_zero_of_correction_zero
    (h : ∀ b : Bad (nativePlaceSelection T),
      normalizedOrderCorrection T b = 0) :
    qCorrectionSum T = 0 := by
  unfold qCorrectionSum
  apply Finset.sum_eq_zero
  intro b _
  rw [h b, zero_mul, mul_zero]

/-- If the actual normalized norm/source data make every correction vanish,
the weighted q-side correction sum is zero. -/
theorem qCorrectionSum_eq_zero_of_normalized_source
    (h : ∀ b : Bad (nativePlaceSelection T),
      qVFamNormRatio T b = 1 ∧
        Real.log (residueNormBase (qVFamTensorPlace T b)) =
          Real.log (qVFamTensorP T b : Real)) :
    qCorrectionSum T = 0 := by
  apply qCorrectionSum_eq_zero_of_correction_zero T
  intro b
  have hb := h b
  have hcorr' : normalizedOrderCorrection T b *
      Real.log (qVFamTensorP T b : Real) =
        ((qVFamily T b).order : Real) *
            (Real.log (residueNormBase (qVFamTensorPlace T b)) -
              Real.log (qVFamTensorP T b : Real)) -
          Real.log (qVFamNormRatio T b) := by
    have hbridge := qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio T b
    unfold normalizedOrderCorrection
    rw [sub_mul, hbridge]
    ring
  have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
  have hzero : normalizedOrderCorrection T b *
      Real.log (qVFamTensorP T b : Real) = 0 := by
    rw [hcorr', hb.2, sub_self, mul_zero, hb.1, Real.log_one, sub_zero]
  exact (mul_eq_zero.mp hzero).resolve_right hlog

/-- Actual absolute-value bound for the weighted q-side correction sum. -/
theorem abs_qCorrectionSum_le :
    |qCorrectionSum T| ≤
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((qVFamily T b).order *
              |Real.log (residueNormBase (qVFamTensorPlace T b)) -
                Real.log (qVFamTensorP T b : Real)| +
            |Real.log (qVFamNormRatio T b)|) := by
  rw [qCorrectionSum_eq_sourceTerm]
  calc
    |∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((qVFamily T b).order *
              (Real.log (residueNormBase (qVFamTensorPlace T b)) -
                Real.log (qVFamTensorP T b : Real)) -
            Real.log (qVFamNormRatio T b))|
        ≤ ∑ b : Bad (nativePlaceSelection T),
            |nativeBadLocalWeight T b *
              ((qVFamily T b).order *
                  (Real.log (residueNormBase (qVFamTensorPlace T b)) -
                    Real.log (qVFamTensorP T b : Real)) -
                Real.log (qVFamNormRatio T b))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((qVFamily T b).order *
              |Real.log (residueNormBase (qVFamTensorPlace T b)) -
                Real.log (qVFamTensorP T b : Real)| +
            |Real.log (qVFamNormRatio T b)|) := by
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul, abs_of_nonneg (badPlaceNativeBadLocalWeight_nonneg T b)]
      apply mul_le_mul_of_nonneg_left ?_ (badPlaceNativeBadLocalWeight_nonneg T b)
      have htri : |((qVFamily T b).order : Real) *
          (Real.log (residueNormBase (qVFamTensorPlace T b)) -
            Real.log (qVFamTensorP T b : Real)) -
          Real.log (qVFamNormRatio T b)| ≤
        |((qVFamily T b).order : Real) *
          (Real.log (residueNormBase (qVFamTensorPlace T b)) -
            Real.log (qVFamTensorP T b : Real))| +
          |Real.log (qVFamNormRatio T b)| := by
        simpa using abs_sub_le
          (((qVFamily T b).order : Real) *
            (Real.log (residueNormBase (qVFamTensorPlace T b)) -
              Real.log (qVFamTensorP T b : Real))) 0
          (Real.log (qVFamNormRatio T b))
      have habs : |((qVFamily T b).order : Real) *
          (Real.log (residueNormBase (qVFamTensorPlace T b)) -
            Real.log (qVFamTensorP T b : Real))| =
          ((qVFamily T b).order : Real) *
            |Real.log (residueNormBase (qVFamTensorPlace T b)) -
              Real.log (qVFamTensorP T b : Real)| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : Real) ≤ ((qVFamily T b).order : Real))]
      rw [habs] at htri
      exact htri

/-- Final S13 coefficient comparison rewritten as the paper-root comparison
plus the explicit correction term. -/
theorem s13Comparison_iff_paperComparison_add_correction :
    (s13ThetaCoefficientSum T ≤ s13QPilotCoefficientSum T) ↔
      (paperThetaCoefficientSum T ≤
        paperQPilotCoefficientSum T +
          (qCorrectionSum T - thetaCorrectionSum T)) := by
  rw [s13ThetaCoefficientSum_eq_paper_add_correction,
    s13QPilotCoefficientSum_eq_paper_add_correction]
  constructor <;> intro h <;> linarith

end LeanFormal.IUT.XiFPaper.BadPlaceCorrectionControlActual
