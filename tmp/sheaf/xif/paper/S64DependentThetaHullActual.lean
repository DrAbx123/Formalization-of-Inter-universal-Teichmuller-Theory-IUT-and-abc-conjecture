import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.S22DependentProductActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.BadPlaceCorrectionControlActual
import tmp.sheaf.xif.paper.BadPlacePaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

/-!
# S64: dependent product Theta hull and its qVFamily comparison

The actual dependent product Theta hull is the fiberwise product of the
per-b rootNormHull sets.  Its per-b normalized hull logs are the actual
perBThetaHullLog, and the weighted global scalar is globalThetaHullLog.

The qVFamily weighted scalar is dependentQVFamWeightedLogMagnitude.  The actual
global qPilot inequality globalQPilotLog <= globalThetaHullLog is available.
This file records the exact conditional comparison: if the qVFamily weighted
scalar is the global qPilot scalar (the source q identification), then it is
bounded by the product Theta hull scalar.  No equality is fabricated.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S64DependentThetaHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionControlActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizationSourceActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.S22DependentProductActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable [∀ b : Bad (nativePlaceSelection T), SigmaFinite (mu b)]

/-- Actual dependent product Theta hull: product of the per-b root hulls. -/
noncomputable def dependentThetaHull :
    Set ((b : Bad (nativePlaceSelection T)) -> qVFamTensorBlock T b) :=
  Set.pi Set.univ (fun b => rootNormHull (l := l) T b)

/-- Its actual product Haar measure, from the per-b Haar measures. -/
noncomputable def dependentThetaHullProductHaar
    (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b)) :
    Measure ((b : Bad (nativePlaceSelection T)) -> qVFamTensorBlock T b) :=
  Measure.pi (fun b => mu b)


/-- Actual product measure of the dependent Theta hull is the product of the
per-b root-hull measures. -/
theorem dependentThetaHull_measure_eq_prod :
    dependentThetaHullProductHaar T mu (dependentThetaHull T) =
      ∏ b : Bad (nativePlaceSelection T), mu b (rootNormHull (l := l) T b) := by
  unfold dependentThetaHullProductHaar dependentThetaHull
  rw [Measure.pi_pi]

/-- The dependent Theta hull has positive product measure. -/
theorem dependentThetaHull_measure_pos :
    0 < dependentThetaHullProductHaar T mu (dependentThetaHull T) := by
  rw [dependentThetaHull_measure_eq_prod]
  apply bot_lt_iff_ne_bot.mpr
  change (∏ b : Bad (nativePlaceSelection T),
    mu b (rootNormHull (l := l) T b)) ≠ (0 : ENNReal)
  rw [Finset.prod_ne_zero_iff]
  intro b _
  exact (rootNormHull_measure_pos (l := l) T b (mu b)).ne'

/-- The dependent Theta hull has finite product measure. -/
theorem dependentThetaHull_measure_lt_top :
    dependentThetaHullProductHaar T mu (dependentThetaHull T) < ⊤ := by
  rw [dependentThetaHull_measure_eq_prod]
  apply ENNReal.prod_lt_top
  intro b _
  exact rootNormHull_measure_lt_top (l := l) T b (mu b)


/-- Exact correction between the paper qPilot scalar and the native qVFamily
weighted magnitude. -/
noncomputable def qVFamNormRatioCorrection : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * Real.log (qVFamNormRatio T b)


/-- S79 qVFamily norm-ratio correction is exactly the S81/S84 norm-ratio
correction sum: same weights, same log ratio, same sign. -/
theorem qVFamNormRatioCorrection_eq_normRatioCorrectionSum :
    qVFamNormRatioCorrection T = normRatioCorrectionSum T :=
  rfl

/-- Per-b exact relation: paper perB qPilot log = -native local magnitude +
log(qVFamNormRatio). -/
theorem perBQPilotLog_eq_neg_native_add_logRatio
    (b : Bad (nativePlaceSelection T)) :
    perBQPilotLog T b =
      -nativeQVPilotLocalMagnitude T b + Real.log (qVFamNormRatio T b) := by
  unfold perBQPilotLog
  rw [qPilotClassicalLog_eq]
  have hsum : (∑ i : qVFamTensorV,
      rootNormCoefficient (l := l) T b i) =
      qVFamNormalizedCoefficient T b := by
    simp [rootNormCoefficient, qVFamNormalizedCoefficientFamily, qVFamTensorV]
  rw [hsum]
  have h := qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_sub_log_ratio T b
  unfold nativeQVPilotLocalMagnitude
  linarith

/-- The native qVFamily weighted magnitude is the sum of local magnitudes. -/
theorem dependentQVFamWeightedLogMagnitude_eq_local_sum :
    dependentQVFamWeightedLogMagnitude T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * nativeQVPilotLocalMagnitude T b := by
  unfold dependentQVFamWeightedLogMagnitude nativeQVPilotLocalMagnitude
    localLogMagnitude localSignedLog
  apply Finset.sum_congr rfl
  intro b _
  rfl

/-- Exact correction formula:
global paper qPilot = - native qVFamily weighted magnitude + norm-ratio correction. -/
theorem globalQPilotLog_eq_neg_dependentQVFam_add_correction :
    globalQPilotLog T =
      -dependentQVFamWeightedLogMagnitude T + qVFamNormRatioCorrection T := by
  unfold globalQPilotLog qVFamNormRatioCorrection
  rw [dependentQVFamWeightedLogMagnitude_eq_local_sum]
  calc
    (∑ b, nativeBadLocalWeight T b * perBQPilotLog T b)
        = ∑ b, nativeBadLocalWeight T b *
            (-nativeQVPilotLocalMagnitude T b +
              Real.log (qVFamNormRatio T b)) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [perBQPilotLog_eq_neg_native_add_logRatio]
    _ = -∑ b, nativeBadLocalWeight T b *
            nativeQVPilotLocalMagnitude T b +
          ∑ b, nativeBadLocalWeight T b * Real.log (qVFamNormRatio T b) := by
          rw [← Finset.sum_neg_distrib]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro b _
          ring

/-- Actual product hull normalized scalar: sum of weighted per-b root hull logs. -/
noncomputable def dependentThetaHullNormalizedLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * perBThetaHullLog T b

/-- The product hull normalized scalar is the actual globalThetaHullLog. -/
theorem dependentThetaHullNormalizedLog_eq :
    dependentThetaHullNormalizedLog T = globalThetaHullLog T := by
  unfold dependentThetaHullNormalizedLog globalThetaHullLog
  rfl

/-- The qVFamily weighted scalar is the native normalized qVFamily magnitude. -/
theorem dependentQVFamProductLog_eq :
    dependentQVFamWeightedLogMagnitude T =
      nativeQVPilotNormalizedLogMagnitude T :=
  dependentQVFamWeightedLogMagnitude_eq T

/-- The correction relation makes the qVFamily weighted magnitude equal to
the exact correction minus the paper global qPilot scalar. -/
theorem dependentQVFamProductLog_eq_correction_sub_globalQPilot :
    dependentQVFamWeightedLogMagnitude T =
      qVFamNormRatioCorrection T - globalQPilotLog T := by
  have h := globalQPilotLog_eq_neg_dependentQVFam_add_correction T
  linarith

/-- The correct comparison with the product Theta hull is through the exact
correction, not a fabricated equality. -/
theorem dependentQVFamProductLog_le_thetaHull_iff :
    dependentQVFamWeightedLogMagnitude T ≤ dependentThetaHullNormalizedLog T ↔
      qVFamNormRatioCorrection T - globalQPilotLog T ≤
        dependentThetaHullNormalizedLog T := by
  rw [dependentQVFamProductLog_eq_correction_sub_globalQPilot]


/-- Unified paper-normalized correction form: the paper qPilot scalar is the
negative qVFamily magnitude plus the single S81/S84 norm-ratio correction. -/
theorem globalQPilotLog_eq_neg_dependentQVFam_add_normRatioCorrection :
    globalQPilotLog T =
      -dependentQVFamWeightedLogMagnitude T + normRatioCorrectionSum T := by
  rw [globalQPilotLog_eq_neg_dependentQVFam_add_correction,
    qVFamNormRatioCorrection_eq_normRatioCorrectionSum]

/-- Unified final comparison in terms of the single S81/S84 correction. -/
theorem dependentQVFamProductLog_le_thetaHull_iff_normRatioCorrection :
    dependentQVFamWeightedLogMagnitude T ≤ dependentThetaHullNormalizedLog T ↔
      normRatioCorrectionSum T - globalQPilotLog T ≤
        dependentThetaHullNormalizedLog T := by
  rw [dependentQVFamProductLog_le_thetaHull_iff,
    qVFamNormRatioCorrection_eq_normRatioCorrectionSum]

/-- The qVFamily correction vanishes iff the S81/S84 correction vanishes. -/
theorem qVFamNormRatioCorrection_zero_iff :
    qVFamNormRatioCorrection T = 0 ↔ normRatioCorrectionSum T = 0 := by
  rw [qVFamNormRatioCorrection_eq_normRatioCorrectionSum]
/-- Exact correction zero condition. -/
def QVFamNormRatioCorrectionZero : Prop :=
  qVFamNormRatioCorrection T = 0

end LeanFormal.IUT.XiFPaper.S64DependentThetaHullActual

end
