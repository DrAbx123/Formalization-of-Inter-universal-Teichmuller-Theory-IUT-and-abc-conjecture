import tmp.sheaf.xif.paper.BadPlacePaperNormalizedComparisonActual

/-! # Actual norm-ratio correction after paper normalization

S81 absorbed the rational degree into paperNormalizedCoefficient.  The only
remaining correction is the normalized/default norm ratio:

  c_norm = paperCoefficient - log(qVFamNormRatio)/log p_b.

This file proves the exact norm-ratio correction in terms of the actual
coefficient difference paperCoefficient - c_norm, gives the absolute bound,
and states the final comparison as the paper-normalized comparison plus the
actual correction.  No degree term is used as a correction.

qVFamNormRatio = 1 is not proved unconditionally; the exact condition and
correction bound are kept.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceNormRatioCorrectionActual

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
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizedSourceHypothesisActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Exact per-b norm-ratio logarithm in terms of the actual coefficient gap. -/
theorem log_qVFamNormRatio_eq_coefficient_gap :
    Real.log (qVFamNormRatio T b) =
      (paperNormalizedCoefficient T b -
          QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b) *
        Real.log (qVFamTensorP T b : Real) := by
  have h := c_norm_eq_paperCoefficient_sub_normRatio T b
  have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
  field_simp [hlog] at h
  linarith

/-- Exact coefficient-gap form of the q-side norm-ratio correction sum. -/
theorem normRatioCorrectionSum_eq_coefficient_gap :
    normRatioCorrectionSum T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((paperNormalizedCoefficient T b -
              QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b) *
            Real.log (qVFamTensorP T b : Real)) := by
  unfold normRatioCorrectionSum
  apply Finset.sum_congr rfl
  intro b _
  rw [log_qVFamNormRatio_eq_coefficient_gap]

/-- Actual absolute bound for the q-side norm-ratio correction. -/
theorem abs_normRatioCorrectionSum_le :
    |normRatioCorrectionSum T| ≤
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (|paperNormalizedCoefficient T b -
              QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b| *
            |Real.log (qVFamTensorP T b : Real)|) := by
  rw [normRatioCorrectionSum_eq_coefficient_gap]
  calc
    |∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((paperNormalizedCoefficient T b -
              QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b) *
            Real.log (qVFamTensorP T b : Real))|
        ≤ ∑ b : Bad (nativePlaceSelection T),
            |nativeBadLocalWeight T b *
              ((paperNormalizedCoefficient T b -
                  QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b) *
                Real.log (qVFamTensorP T b : Real))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (|paperNormalizedCoefficient T b -
              QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b| *
            |Real.log (qVFamTensorP T b : Real)|) := by
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul, abs_mul,
        abs_of_nonneg (badPlaceNativeBadLocalWeight_nonneg T b)]

/-- The Theta-side half correction is exactly the q-side correction divided by
2l. -/
theorem twoL_mul_halfNormRatioCorrectionSum :
    (2 * l.value : Real) * halfNormRatioCorrectionSum T =
      normRatioCorrectionSum T := by
  unfold halfNormRatioCorrectionSum normRatioCorrectionSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  have hl : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.prime.ne_zero
  field_simp [htwo, hl]

/-- Exact actual correction term in the final paper-normalized comparison. -/
theorem finalComparison_iff_paperNormalized_add_actualCorrection :
    (s13ThetaCoefficientSum T ≤ s13QPilotCoefficientSum T) ↔
      (paperNormalizedThetaSum T ≤
        paperNormalizedQPilotSum T +
          (halfNormRatioCorrectionSum T - normRatioCorrectionSum T)) :=
  s13Comparison_iff_paperNormalized_add_normRatio T

/-- If the normalized/default norm ratio is one at every bad place, both
norm-ratio corrections vanish and the final comparison is exactly the
paper-normalized comparison. -/
theorem finalComparison_iff_paperNormalized_of_normRatio_one
    (h : ∀ b : Bad (nativePlaceSelection T), qVFamNormRatio T b = 1) :
    (s13ThetaCoefficientSum T ≤ s13QPilotCoefficientSum T) ↔
      (paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T) := by
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
  rw [finalComparison_iff_paperNormalized_add_actualCorrection,
    hnorm, hhalf]
  constructor <;> intro hle <;> linarith

end LeanFormal.IUT.XiFPaper.BadPlaceNormRatioCorrectionActual
