import tmp.sheaf.xif.paper.BadPlaceProcessionNormalizedComparisonActual
/-! # S153 is a model comparison, not the Cor3.12 paper qPilot
IUT III line 7475 uses the classical valuation log
  log(q) = ord_v(q_v) * log p_v,
equivalently the paper coefficient order * log(residueNormBase F-place), not the
normalized spectral coefficient c_norm.  The exact actual bridge is
  c_norm_b * log p_b = order_b * log(residueNormBase_b) - log(qVFamNormRatio_b).
Thus S153's processionNormalizedComparison is identified with the paper Cor3.12
qPilot comparison exactly when the norm-ratio correction vanishes; otherwise it
is only an intermediate model comparison and must not be called the Cor3.12
target.  No norm equality is faked. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.BadPlaceS153ModelOnlyActual
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
open LeanFormal.IUT.XiFPaper.BadPlaceProcessionNormalizedComparisonActual
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
/-- The paper/classical qPilot log: order times log residueNormBase, IUT III
line 7475, not the normalized spectral coefficient. -/
noncomputable def paperClassicalQPilotLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (((qVFamily T b).order : Real) *
        Real.log (residueNormBase (qVFamTensorPlace T b)))
/-- Exact per-b gap: the normalized coefficient differs from the paper classical
coefficient by the norm-ratio logarithm. -/
theorem normalizedCoefficient_gap (b : Bad (nativePlaceSelection T)) :
    QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
        Real.log (qVFamTensorP T b : Real) =
      ((qVFamily T b).order : Real) *
          Real.log (residueNormBase (qVFamTensorPlace T b)) -
        Real.log (qVFamNormRatio T b) :=
  qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio T b
/-- Exact scalar gap: normalized qPilot log = paper classical qPilot log minus the
norm-ratio correction sum. -/
theorem processionNormalizedQPilot_eq_paperClassical_sub_correction :
    processionNormalizedQPilotLog T =
      paperClassicalQPilotLog T - normRatioCorrectionSum T := by
  unfold processionNormalizedQPilotLog paperClassicalQPilotLog normRatioCorrectionSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [normalizedCoefficient_gap T b]
  ring
/-- S153's qPilot is the paper qPilot exactly when the norm-ratio correction
sum vanishes. -/
theorem processionNormalizedQPilot_eq_paperClassical_iff :
    processionNormalizedQPilotLog T = paperClassicalQPilotLog T ↔
      normRatioCorrectionSum T = 0 := by
  rw [processionNormalizedQPilot_eq_paperClassical_sub_correction]
  constructor <;> intro h <;> linarith
/-- S153 model comparison identification with the paper qPilot. -/
def S153Cor312QPilotIdentification : Prop :=
  processionNormalizedQPilotLog T = paperClassicalQPilotLog T
/-- If the norm-ratio correction is nonzero, S153's qPilot is NOT the paper
classical qPilot. -/
theorem s153_not_cor312_of_correction_ne_zero
    (h : normRatioCorrectionSum T ≠ 0) :
    ¬ S153Cor312QPilotIdentification T := by
  intro hident
  exact h ((processionNormalizedQPilot_eq_paperClassical_iff T).mp hident)
/-- If the correction vanishes, the identification holds. -/
theorem s153_cor312_identification_of_correction_eq_zero
    (h : normRatioCorrectionSum T = 0) :
    S153Cor312QPilotIdentification T :=
  (processionNormalizedQPilot_eq_paperClassical_iff T).mpr h
/-- S153's comparison is marked as a model comparison unless the identification
holds; it is not asserted as the Cor3.12 paper target in general. -/
theorem s153_comparison_model_only_unless_identification :
    (¬ S153Cor312QPilotIdentification T) →
      ¬ (processionNormalizedQPilotLog T = paperClassicalQPilotLog T) := by
  intro h h_eq
  exact h h_eq
end LeanFormal.IUT.XiFPaper.BadPlaceS153ModelOnlyActual
