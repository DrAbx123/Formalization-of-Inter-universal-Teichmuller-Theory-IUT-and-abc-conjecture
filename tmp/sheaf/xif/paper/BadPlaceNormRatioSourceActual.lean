import tmp.sheaf.xif.paper.BadPlacePaperNormalizedActual

/-! # Norm-ratio source condition and correction-controlled conclusion

qVFamNormRatio is the quotient of the normalized and default completion norms
on the same qVFamily element.  Its definition does not force it to be one;
the exact equivalent is paperNormalizedCoefficient = c_norm.  This file proves
that exact characterization and uses the S85 correction bound to state the
actual paper-normalized comparison within the actual correction bound, or
within any epsilon controlling that bound.

No fake qVFamNormRatio = 1. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceNormRatioSourceActual

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
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The norm ratio is one exactly when the paper-normalized coefficient equals
the normalized supply coefficient. -/
theorem qVFamNormRatio_eq_one_iff_paperCoefficient_eq_cNorm :
    qVFamNormRatio T b = 1 ↔
      paperNormalizedCoefficient T b =
        QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b := by
  have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
  have hgap := log_qVFamNormRatio_eq_coefficient_gap T b
  constructor
  · intro h
    rw [h, Real.log_one] at hgap
    have hzero : paperNormalizedCoefficient T b -
        QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b = 0 :=
      (mul_eq_zero.mp hgap.symm).resolve_right hlog
    linarith
  · intro h
    rw [h, sub_self, zero_mul] at hgap
    have hratio_pos : 0 < qVFamNormRatio T b := by
      unfold qVFamNormRatio qVFamNormalizedNorm qVFamDefaultNorm
      exact div_pos
        (norm_pos_iff.mpr (qVFamNormalizedGenerator_ne_zero T b))
        (norm_pos_iff.mpr (qVFamily T b).q_ne_zero)
    rcases (Real.log_eq_zero.mp hgap) with h0 | h1 | hneg
    · linarith
    · exact h1
    · linarith

/-- If every paper-normalized coefficient agrees with c_norm, the norm-ratio
gap bound is zero. -/
theorem normRatioGapBound_eq_zero_of_paper_eq_cNorm
    (h : ∀ b : Bad (nativePlaceSelection T),
      paperNormalizedCoefficient T b =
        QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b) :
    normRatioGapBound T = 0 := by
  unfold normRatioGapBound
  apply Finset.sum_eq_zero
  intro b _
  rw [h b, sub_self, abs_zero, zero_mul, mul_zero]

/-- Actual conclusion within the correction bound: the paper-normalized
comparison holds up to the actual norm-ratio gap bound. -/
theorem paperNormalizedComparison_within_gapBound :
    paperNormalizedThetaSum T ≤
      paperNormalizedQPilotSum T + normRatioGapBound T := by
  have hcomp := paperNormalizedComparison_with_correction T
  have hbound := abs_paperNormalizedCorrection_le_gap T
  have hle : paperNormalizedCorrection T ≤ |paperNormalizedCorrection T| := le_abs_self _
  linarith

/-- Controlled regime: if the norm-ratio gap bound is at most epsilon, the
paper-normalized comparison holds within epsilon. -/
theorem paperNormalizedComparison_within_epsilon
    (epsilon : Real) (h : normRatioGapBound T ≤ epsilon) :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T + epsilon := by
  linarith [paperNormalizedComparison_within_gapBound T, h]

/-- If the actual correction is nonpositive, the paper-normalized comparison
is exact without any norm-ratio correction. -/
theorem paperNormalizedComparison_exact_of_correction_nonpos
    (h : paperNormalizedCorrection T ≤ 0) :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T := by
  have hcomp := paperNormalizedComparison_with_correction T
  linarith

/-- Exact source condition for the zero-correction paper comparison. -/
def NormRatioOneSourceCondition : Prop :=
  ∀ b : Bad (nativePlaceSelection T), qVFamNormRatio T b = 1

theorem paperNormalizedComparison_exact_of_sourceCondition
    (h : NormRatioOneSourceCondition T) :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T :=
  paperNormalizedComparison_exact_of_normRatio_one T h

end LeanFormal.IUT.XiFPaper.BadPlaceNormRatioSourceActual
