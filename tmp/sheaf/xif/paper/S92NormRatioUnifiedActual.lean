import tmp.sheaf.xif.paper.BadPlaceNormRatioCorrectionActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual

/-!
# S92: unified qVFam norm-ratio and norm-ratio correction

This file expands the actual definitions

  qVFamNormRatio = ||q||_normalized / ||q||_default

and records the exact criterion qVFamNormRatio = 1.  The unified correction is
the S84 coefficient-gap form

  normRatioCorrectionSum
    = sum_b weight_b * (paperNormalizedCoefficient_b - c_norm_b) * log p_b.

No unconditional qVFamNormRatio = 1 is asserted; the exact zero criterion is
the coefficient equality, and the actual absolute bound is the S84 bound.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S92NormRatioUnifiedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioCorrectionActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Exact unfolding of qVFamNormRatio. -/
theorem qVFamNormRatio_eq_normalized_div_default
    (b : Bad (nativePlaceSelection T)) :
    qVFamNormRatio T b =
      qVFamNormalizedNorm T b / qVFamDefaultNorm T b :=
  rfl

/-- The default qVFamily norm is positive. -/
theorem qVFamDefaultNorm_pos (b : Bad (nativePlaceSelection T)) :
    0 < qVFamDefaultNorm T b := by
  unfold qVFamDefaultNorm
  exact norm_pos_iff.mpr (qVFamily T b).q_ne_zero

/-- The normalized qVFamily norm is positive. -/
theorem qVFamNormalizedNorm_pos (b : Bad (nativePlaceSelection T)) :
    0 < qVFamNormalizedNorm T b := by
  unfold qVFamNormalizedNorm
  exact norm_pos_iff.mpr (qVFamNormalizedGenerator_ne_zero T b)

/-- qVFamNormRatio is positive. -/
theorem qVFamNormRatio_pos (b : Bad (nativePlaceSelection T)) :
    0 < qVFamNormRatio T b := by
  unfold qVFamNormRatio
  exact div_pos (qVFamNormalizedNorm_pos T b) (qVFamDefaultNorm_pos T b)

/-- Exact criterion for qVFamNormRatio = 1: the normalized and default norms
agree on the actual qVFamily element. -/
theorem qVFamNormRatio_eq_one_iff
    (b : Bad (nativePlaceSelection T)) :
    qVFamNormRatio T b = 1 ↔ QVFamNormInstanceGap T b := by
  unfold qVFamNormRatio QVFamNormInstanceGap
  rw [div_eq_one_iff_eq (ne_of_gt (qVFamDefaultNorm_pos T b))]

/-- Exact coefficient-gap form of the unified correction. -/
theorem normRatioCorrectionSum_eq_paper_sub_cNorm :
    normRatioCorrectionSum T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((paperNormalizedCoefficient T b -
              qVFamNormalizedCoefficient T b) *
            Real.log (qVFamTensorP T b : Real)) :=
  BadPlaceNormRatioCorrectionActual.normRatioCorrectionSum_eq_coefficient_gap T

/-- Actual S84 absolute bound for the unified correction. -/
theorem abs_normRatioCorrectionSum_le :
    |normRatioCorrectionSum T| ≤
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (|paperNormalizedCoefficient T b -
              qVFamNormalizedCoefficient T b| *
            |Real.log (qVFamTensorP T b : Real)|) :=
  BadPlaceNormRatioCorrectionActual.abs_normRatioCorrectionSum_le T

/-- Exact zero criterion: if paperNormalizedCoefficient equals c_norm at every
bad place, the unified norm-ratio correction vanishes. -/
theorem normRatioCorrectionSum_eq_zero_of_coefficient_eq
    (h : ∀ b : Bad (nativePlaceSelection T),
      paperNormalizedCoefficient T b = qVFamNormalizedCoefficient T b) :
    normRatioCorrectionSum T = 0 := by
  rw [normRatioCorrectionSum_eq_paper_sub_cNorm]
  apply Finset.sum_eq_zero
  intro b _
  rw [h b, sub_self, zero_mul, mul_zero]

/-- The actual zero criterion in coefficient-gap form. -/
def NormRatioCorrectionZeroCriterion : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    paperNormalizedCoefficient T b = qVFamNormalizedCoefficient T b

end LeanFormal.IUT.XiFPaper.S92NormRatioUnifiedActual

end
