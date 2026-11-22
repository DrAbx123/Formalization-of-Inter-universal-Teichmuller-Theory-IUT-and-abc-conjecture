import tmp.sheaf.xif.paper.BadPlaceThetaHullScalarBridgeActual

/-! # Exact root-hull coefficient correction formula

The S114 correction is expanded per bad place:

  thetaHullCoefficientCorrection
    = - sum_b w_b * ( actualLocalHullLog_b + (c_norm_b/(2l))*log p_b ).

The bracket is the exact root-hull scaling/coefficient gap.  If the actual
root-hull scaling-data formula identifies actualLocalHullLog_b with
-((c_norm_b/(2l))*log p_b), the correction vanishes.  Otherwise this exact gap
and its absolute bound remain.  No fake correction = 0.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceThetaHullCorrectionFormulaActual

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
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetBridgeActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The coefficient contribution used by s13ThetaCoefficientSum at b. -/
noncomputable def thetaCoefficientContribution : Real :=
  (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
      (2 * l.value : Real)) * Real.log (qVFamTensorP T b : Real)

/-- Exact root-hull scaling/coefficient gap at b. -/
noncomputable def rootHullCoefficientGap : Real :=
  actualLocalHullLog (l := l) T b + thetaCoefficientContribution T b

/-- Exact formula: the S114 correction is minus the weighted sum of these gaps. -/
theorem thetaHullCoefficientCorrection_eq_neg_sum_gap :
    thetaHullCoefficientCorrection (l := l) T =
      - ∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * rootHullCoefficientGap T b := by
  unfold thetaHullCoefficientCorrection actualThetaHullMagnitudeRoot
    actualThetaHullLogRoot s13ThetaCoefficientSum rootHullCoefficientGap
    thetaCoefficientContribution
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

/-- Actual root-hull scaling formula hypothesis at b. -/
def RootHullScalingFormulaAt : Prop :=
  actualLocalHullLog (l := l) T b = -thetaCoefficientContribution T b

/-- If all actual root-hull scaling formulas hold, the correction vanishes. -/
theorem thetaHullCoefficientCorrection_eq_zero_of_scaling_formula
    (h : ∀ b : Bad (nativePlaceSelection T), RootHullScalingFormulaAt T b) :
    thetaHullCoefficientCorrection (l := l) T = 0 := by
  rw [thetaHullCoefficientCorrection_eq_neg_sum_gap]
  have hzero : (∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b * rootHullCoefficientGap T b) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    unfold rootHullCoefficientGap
    rw [(h b)]
    ring
  rw [hzero, neg_zero]

/-- Absolute bound of the correction by the exact root-hull gap. -/
theorem abs_thetaHullCoefficientCorrection_le :
    |thetaHullCoefficientCorrection (l := l) T| ≤
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * |rootHullCoefficientGap T b| := by
  rw [thetaHullCoefficientCorrection_eq_neg_sum_gap, abs_neg]
  calc
    |∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * rootHullCoefficientGap T b|
        ≤ ∑ b : Bad (nativePlaceSelection T),
            |nativeBadLocalWeight T b * rootHullCoefficientGap T b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * |rootHullCoefficientGap T b| := by
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul, abs_of_nonneg (badPlaceNativeBadLocalWeight_nonneg T b)]

end LeanFormal.IUT.XiFPaper.BadPlaceThetaHullCorrectionFormulaActual
