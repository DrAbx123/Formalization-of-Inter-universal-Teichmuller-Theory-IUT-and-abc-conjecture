import tmp.sheaf.xif.paper.BadPlacePaperNormalizedTargetBridgeActual

/-! # Exact Theta-hull scalar bridge correction

The Theta-side scalar bridge is the exact difference

  thetaCorrection = actualThetaHullMagnitudeRoot - s13ThetaCoefficientSum.

This file records that difference without pretending it is zero, and rewrites
the target bridge exactly as

  paper comparison iff
    actualThetaMag <= actualQPilotMag + (normRatioCorrection - halfNormRatioCorrection + thetaCorrection).

If the total correction is nonpositive, paper comparison implies the actual
magnitude target.  No fake bridge.

No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceThetaHullScalarBridgeActual

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
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
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

/-- Exact Theta-hull coefficient scalar correction. -/
noncomputable def thetaHullCoefficientCorrection : Real :=
  actualThetaHullMagnitudeRoot (l := l) T - s13ThetaCoefficientSum T

/-- The Theta bridge is exactly the vanishing of the correction. -/
theorem ThetaHullCoefficientScalarBridge_iff_correction_zero :
    ThetaHullCoefficientScalarBridge T ↔ thetaHullCoefficientCorrection T = 0 := by
  unfold ThetaHullCoefficientScalarBridge thetaHullCoefficientCorrection
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Exact target bridge with the actual Theta scalar correction. -/
theorem paperComparison_iff_actualMagnitude_add_thetaCorrection :
    (paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T) ↔
      (actualThetaHullMagnitudeRoot (l := l) T ≤
        actualQPilotMagnitudeClassical (l := l) T +
          (normRatioCorrectionSum T - halfNormRatioCorrectionSum T +
            thetaHullCoefficientCorrection T)) := by
  have hq := paperNormalizedQPilotSum_eq_actual_add_normRatio T
  have ht := paperNormalizedThetaSum_eq_s13Theta_add_halfNormRatio T
  unfold thetaHullCoefficientCorrection
  constructor <;> intro h <;> linarith

/-- If the total actual correction is nonpositive, the exact paper-normalized
comparison implies the actual magnitude target. -/
theorem actualTargetMagnitude_of_paperComparison_of_totalCorrection_nonpos
    (hcorr : normRatioCorrectionSum T - halfNormRatioCorrectionSum T +
      thetaHullCoefficientCorrection T ≤ 0) :
    actualThetaHullMagnitudeRoot (l := l) T ≤
      actualQPilotMagnitudeClassical (l := l) T := by
  have hpaper := paperNormalizedThetaSum_le_qPilotSum_direct T
  have h := (paperComparison_iff_actualMagnitude_add_thetaCorrection T).mp hpaper
  linarith

end LeanFormal.IUT.XiFPaper.BadPlaceThetaHullScalarBridgeActual
