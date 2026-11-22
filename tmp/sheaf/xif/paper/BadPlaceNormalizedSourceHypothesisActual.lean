import tmp.sheaf.xif.paper.BadPlaceCorrectionControlActual
import tmp.sheaf.xif.paper.QVFamTensorBlockAlignmentActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-! # Checking the S45 normalized-source hypothesis

S45 used the hypothesis

  1) qVFamNormRatio_b = 1
  2) log(residueNormBase F-place_b) = log p_b.

This file proves the exact equivalent of (1) via the actual normalized-norm
bridge, proves (2) is equivalent to rational degree one under the actual
rational-prime log obstruction, and derives the paper-root comparison under the
combined hypothesis.  It also records the failure criterion when the rational
degree is not one.  Nothing is assumed unconditionally.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceNormalizedSourceHypothesisActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizationSourceActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootComparisonActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionControlActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual positivity of the normalized/default norm ratio. -/
theorem qVFamNormRatio_pos (b : Bad (nativePlaceSelection T)) :
    0 < qVFamNormRatio T b := by
  unfold qVFamNormRatio qVFamNormalizedNorm qVFamDefaultNorm
  exact div_pos
    (norm_pos_iff.mpr (qVFamNormalizedGenerator_ne_zero T b))
    (norm_pos_iff.mpr (qVFamily T b).q_ne_zero)

/-- Condition (1) is exactly the equality of the q-side coefficient contributions. -/
theorem qVFamNormRatio_eq_one_iff (b : Bad (nativePlaceSelection T)) :
    qVFamNormRatio T b = 1 ↔
      QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
          Real.log (qVFamTensorP T b : Real) =
        ((qVFamily T b).order : Real) *
          Real.log (residueNormBase (qVFamTensorPlace T b)) := by
  constructor
  · intro h
    have hlog : Real.log (qVFamNormRatio T b) = 0 := by rw [h, Real.log_one]
    have hbridge := qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio T b
    linarith
  · intro h
    have hlog : Real.log (qVFamNormRatio T b) = 0 := by
      have hbridge := qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio T b
      linarith
    have hpos := qVFamNormRatio_pos T b
    rcases (Real.log_eq_zero.mp hlog) with h0 | h1 | hneg
    · linarith
    · exact h1
    · linarith

/-- Condition (2) follows from the actual rational-prime log obstruction and
rational degree one. -/
theorem logResidueNormBase_eq_logP_of_obstruction_degree_one
    (b : Bad (nativePlaceSelection T))
    (hobs : qVFamTensorRationalPrimeLogObstruction T b)
    (hdeg : qVFamTensorRationalDegree T b = 1) :
    Real.log (residueNormBase (qVFamTensorPlace T b)) =
      Real.log (qVFamTensorP T b : Real) := by
  unfold qVFamTensorRationalPrimeLogObstruction at hobs
  rw [hdeg] at hobs
  simpa using hobs.symm

/-- Under the actual obstruction, condition (2) is equivalent to rational
degree one. -/
theorem logResidueNormBase_eq_logP_iff_degree_one_of_obstruction
    (b : Bad (nativePlaceSelection T))
    (hobs : qVFamTensorRationalPrimeLogObstruction T b) :
    Real.log (residueNormBase (qVFamTensorPlace T b)) =
        Real.log (qVFamTensorP T b : Real) ↔
      qVFamTensorRationalDegree T b = 1 := by
  constructor
  · intro h
    unfold qVFamTensorRationalPrimeLogObstruction at hobs
    have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
      · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
    have hdeg : (qVFamTensorRationalDegree T b : Real) *
        Real.log (qVFamTensorP T b : Real) =
          Real.log (qVFamTensorP T b : Real) := by
      simpa [h] using hobs
    have hsub : ((qVFamTensorRationalDegree T b : Real) - 1) *
        Real.log (qVFamTensorP T b : Real) = 0 := by linarith
    have hdeg_real : (qVFamTensorRationalDegree T b : Real) = 1 := by
      have hzero : (qVFamTensorRationalDegree T b : Real) - 1 = 0 :=
        (mul_eq_zero.mp hsub).resolve_right hlog
      linarith
    exact_mod_cast hdeg_real
  · intro hdeg
    exact logResidueNormBase_eq_logP_of_obstruction_degree_one T b hobs hdeg

/-- The exact S45 normalized-source hypothesis. -/
def NormalizedSourceHypothesis : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    qVFamNormRatio T b = 1 ∧
      Real.log (residueNormBase (qVFamTensorPlace T b)) =
        Real.log (qVFamTensorP T b : Real)

/-- The hypothesis follows from the q-side coefficient equality, the actual
rational-prime log obstruction and rational degree one. -/
theorem normalizedSourceHypothesis_of_ratio_and_obstruction_degree
    (hratio : ∀ b : Bad (nativePlaceSelection T),
      QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
          Real.log (qVFamTensorP T b : Real) =
        ((qVFamily T b).order : Real) *
          Real.log (residueNormBase (qVFamTensorPlace T b)))
    (hobs : ∀ b : Bad (nativePlaceSelection T),
      qVFamTensorRationalPrimeLogObstruction T b)
    (hdeg : ∀ b : Bad (nativePlaceSelection T),
      qVFamTensorRationalDegree T b = 1) :
    NormalizedSourceHypothesis T := by
  intro b
  exact ⟨(qVFamNormRatio_eq_one_iff T b).mpr (hratio b),
    logResidueNormBase_eq_logP_of_obstruction_degree_one T b (hobs b) (hdeg b)⟩

/-- If the rational degree at b is not one and the obstruction holds, condition
(2) fails: a concrete failure criterion. -/
theorem normalizedSourceHypothesis_fails_of_degree_ne_one
    (b : Bad (nativePlaceSelection T))
    (hobs : qVFamTensorRationalPrimeLogObstruction T b)
    (hdeg : qVFamTensorRationalDegree T b ≠ 1) :
    ¬ (qVFamNormRatio T b = 1 ∧
      Real.log (residueNormBase (qVFamTensorPlace T b)) =
        Real.log (qVFamTensorP T b : Real)) := by
  intro h
  exact hdeg ((logResidueNormBase_eq_logP_iff_degree_one_of_obstruction T b hobs).mp h.2)

/-- Under the normalized-source hypothesis the q-side correction sum vanishes. -/
theorem qCorrectionSum_eq_zero_of_hypothesis
    (h : NormalizedSourceHypothesis T) :
    qCorrectionSum T = 0 :=
  qCorrectionSum_eq_zero_of_normalized_source T h

/-- Under the normalized-source hypothesis the Theta-side correction also
vanishes. -/
theorem thetaCorrectionSum_eq_zero_of_hypothesis
    (h : NormalizedSourceHypothesis T) :
    thetaCorrectionSum T = 0 :=
  (qCorrection_zero_iff_thetaCorrection_zero T).mp
    (qCorrectionSum_eq_zero_of_hypothesis T h)

/-- Under the normalized-source hypothesis S13 q-coefficient sum equals the
paper root constant sum. -/
theorem s13Q_eq_paper_of_hypothesis
    (h : NormalizedSourceHypothesis T) :
    s13QPilotCoefficientSum T = paperQPilotCoefficientSum T := by
  exact (s13Q_eq_paper_iff_qCorrection_zero T).mpr
    (qCorrectionSum_eq_zero_of_hypothesis T h)

/-- Under the normalized-source hypothesis the final S13 coefficient comparison
is exactly the paper-root comparison. -/
theorem s13Comparison_iff_paperComparison_of_hypothesis
    (h : NormalizedSourceHypothesis T) :
    (s13ThetaCoefficientSum T ≤ s13QPilotCoefficientSum T) ↔
      (paperThetaCoefficientSum T ≤ paperQPilotCoefficientSum T) := by
  have hq := s13Q_eq_paper_of_hypothesis T h
  have ht := (s13Theta_eq_paper_iff_thetaCorrection_zero T).mpr
    (thetaCorrectionSum_eq_zero_of_hypothesis T h)
  rw [hq, ht]

/-- Without the hypothesis, the actual final comparison remains the
paper-root comparison plus the explicit correction term. -/
theorem s13Comparison_iff_paperComparison_add_correction_remaining :
    (s13ThetaCoefficientSum T ≤ s13QPilotCoefficientSum T) ↔
      (paperThetaCoefficientSum T ≤
        paperQPilotCoefficientSum T +
          (qCorrectionSum T - thetaCorrectionSum T)) :=
  s13Comparison_iff_paperComparison_add_correction T

end LeanFormal.IUT.XiFPaper.BadPlaceNormalizedSourceHypothesisActual
