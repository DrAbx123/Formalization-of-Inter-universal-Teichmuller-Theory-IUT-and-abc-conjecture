import tmp.sheaf.xif.paper.BadPlaceCorrectionSignAttackActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetBridgeActual

/-! # Bridge from paper-normalized scalars to the actual target

This file connects S102's exact paper-normalized comparison with the existing
ActualPaperXiFTarget scalars.  The q-side bridge is actual and exact:
paperNormalizedQPilotSum = actualQPilotMagnitudeClassical + normRatioCorrectionSum.
The Theta side has an exact scalar bridge condition
actualThetaHullMagnitudeRoot = s13ThetaCoefficientSum; this is recorded, not
faked.  Under that scalar bridge we identify the correction in the actual
target comparison.

Direction, weights, the 1/(2l) root factor and log p constants are checked.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedTargetBridgeActual

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

/-- q-side bridge: actual qPilot magnitude is the S13 q coefficient sum. -/
theorem actualQPilotMagnitude_eq_s13Q :
    actualQPilotMagnitudeClassical (l := l) T = s13QPilotCoefficientSum T := rfl

/-- paperNormalizedQPilotSum = actual qPilot magnitude + norm-ratio correction. -/
theorem paperNormalizedQPilotSum_eq_actual_add_normRatio :
    paperNormalizedQPilotSum T =
      actualQPilotMagnitudeClassical (l := l) T +
        normRatioCorrectionSum T := by
  have h := s13Q_eq_paperNormalized_sub_normRatio T
  rw [actualQPilotMagnitude_eq_s13Q]
  linarith

/-- paperNormalizedThetaSum = S13 Theta coefficient sum + half norm-ratio. -/
theorem paperNormalizedThetaSum_eq_s13Theta_add_halfNormRatio :
    paperNormalizedThetaSum T =
      s13ThetaCoefficientSum T + halfNormRatioCorrectionSum T := by
  have h := s13Theta_eq_paperNormalized_sub_halfNormRatio T
  linarith

/-- Exact scalar bridge condition for the Theta hull magnitude. -/
def ThetaHullCoefficientScalarBridge : Prop :=
  actualThetaHullMagnitudeRoot (l := l) T = s13ThetaCoefficientSum T

/-- Under the exact Theta scalar bridge, the paper-normalized comparison is
exactly the actual magnitude comparison plus the norm-ratio correction term. -/
theorem paperComparison_iff_actualMagnitude_add_correction
    (hbridge : ThetaHullCoefficientScalarBridge T) :
    (paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T) ↔
      (actualThetaHullMagnitudeRoot (l := l) T ≤
        actualQPilotMagnitudeClassical (l := l) T +
          (normRatioCorrectionSum T - halfNormRatioCorrectionSum T)) := by
  rw [paperNormalizedQPilotSum_eq_actual_add_normRatio,
    paperNormalizedThetaSum_eq_s13Theta_add_halfNormRatio]
  unfold ThetaHullCoefficientScalarBridge at hbridge
  rw [← hbridge]
  constructor <;> intro h <;> linarith

/-- If the norm-ratio correction is at most the half correction, the exact
paper-normalized comparison implies the actual magnitude target. -/
theorem actualTargetMagnitude_of_paperComparison
    (hbridge : ThetaHullCoefficientScalarBridge T)
    (hcorr : normRatioCorrectionSum T ≤ halfNormRatioCorrectionSum T) :
    actualThetaHullMagnitudeRoot (l := l) T ≤
      actualQPilotMagnitudeClassical (l := l) T :=
  by
    have hpaper := paperNormalizedThetaSum_le_qPilotSum_direct T
    have h := (paperComparison_iff_actualMagnitude_add_correction T hbridge).mp hpaper
    linarith

/-- The actual paper xi-f target is already proven for the actual source
target; this records it in magnitude form. -/
theorem actualPaperXiFTargetMagnitude_actual :
    ActualPaperXiFTargetMagnitude (l := l) T :=
  (actualPaperXiFTarget_iff_magnitude (l := l) T).mp
    (PaperLevelXiFTargetBridgeActual.actualPaperXiFTarget (l := l) T)

end LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedTargetBridgeActual
