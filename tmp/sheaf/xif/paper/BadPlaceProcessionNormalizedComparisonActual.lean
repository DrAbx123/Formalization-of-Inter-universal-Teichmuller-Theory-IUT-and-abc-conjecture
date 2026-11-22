import tmp.sheaf.xif.paper.BadPlacePaperNormalizedTargetBridgeActual
/-! # Procession-normalized qPilot / Theta comparison

Paper Cor3.12 compares the q-pilot and Theta hull with the SAME procession-
normalized mu_log.  The qPilot coefficient is therefore the normalized
coefficient c_norm = qVFamNormalizedCoefficient, not the paper logarithmic
coefficient order * log(residueNormBase)/log p.  This file defines the
procession-normalized qPilot and Theta scalars directly from c_norm and proves
the exact comparison.  The old paperNormalized coefficients differ only by the
diagnostic norm-ratio correction; that correction is definitionally absent
from the new target.

QVFamNormInstanceGap is diagnostic only and is not used in the target.
No fake norm equality. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.BadPlaceProcessionNormalizedComparisonActual
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
open MeasureTheory
open LeanFormal.IUT.ArithmeticQPilotBaseChange
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
/-- Procession-normalized qPilot log: the same mu_log normalization as the
Theta hull. -/
noncomputable def processionNormalizedQPilotLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
        Real.log (qVFamTensorP T b : Real))
/-- Procession-normalized Theta log: same c_norm mu_log with the 1/(2l) root
coefficient. -/
noncomputable def processionNormalizedThetaLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      ((QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
          (2 * l.value : Real)) * Real.log (qVFamTensorP T b : Real))
/-- The normalized qPilot scalar is exactly the existing actual qPilot
magnitude, definitionally. -/
theorem processionNormalizedQPilotLog_eq_actual :
    processionNormalizedQPilotLog T =
      actualQPilotMagnitudeClassical (l := l) T := rfl
/-- The normalized Theta scalar is exactly the S13 Theta coefficient sum. -/
theorem processionNormalizedThetaLog_eq_s13 :
    processionNormalizedThetaLog T = s13ThetaCoefficientSum T := rfl
/-- Exact Cor3.12 magnitude comparison with the same procession-normalized
mu_log. -/
theorem processionNormalizedComparison :
    processionNormalizedThetaLog T ≤ processionNormalizedQPilotLog T := by
  unfold processionNormalizedThetaLog processionNormalizedQPilotLog
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
    have hp : Nat.Prime (qVFamTensorP T b) := Fact.out
    exact_mod_cast hp.one_le
/-- Signed form: -qPilot <= -Theta, the actual Cor3.12 direction. -/
theorem processionNormalizedComparison_signed :
    -processionNormalizedQPilotLog T ≤ -processionNormalizedThetaLog T := by
  linarith [processionNormalizedComparison T]
/-- Old paperNormalized qPilot is the normalized scalar plus the diagnostic
norm-ratio correction. -/
theorem oldPaperNormalizedQPilot_eq_normalized_add_correction :
    paperNormalizedQPilotSum T =
      processionNormalizedQPilotLog T + normRatioCorrectionSum T := by
  have h := paperNormalizedQPilotSum_eq_actual_add_normRatio T
  rw [processionNormalizedQPilotLog_eq_actual]
  linarith
/-- Old paperNormalized Theta is the normalized scalar plus the diagnostic half
correction. -/
theorem oldPaperNormalizedTheta_eq_normalized_add_half :
    paperNormalizedThetaSum T =
      processionNormalizedThetaLog T + halfNormRatioCorrectionSum T := by
  have h := paperNormalizedThetaSum_eq_s13Theta_add_halfNormRatio T
  rw [processionNormalizedThetaLog_eq_s13]
  linarith
/-- The procession-normalized target is exactly the signed Cor3.12 comparison
with no norm-ratio correction term. -/
def ProcessionNormalizedTarget : Prop :=
  processionNormalizedThetaLog T ≤ processionNormalizedQPilotLog T
theorem processionNormalizedTarget_iff_signed :
    ProcessionNormalizedTarget T ↔
      -processionNormalizedQPilotLog T ≤ -processionNormalizedThetaLog T := by
  unfold ProcessionNormalizedTarget
  constructor <;> intro h <;> linarith
theorem processionNormalizedTarget_actual : ProcessionNormalizedTarget T :=
  processionNormalizedComparison T
end LeanFormal.IUT.XiFPaper.BadPlaceProcessionNormalizedComparisonActual
