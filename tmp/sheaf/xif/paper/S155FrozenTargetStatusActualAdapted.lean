import tmp.sheaf.xif.paper.S145NormRatioCorrectionZeroActual
import tmp.sheaf.xif.paper.S154PaperNormalizedQUnitActual

/-!
# S155: frozen-target status

The frozen q-pilot target is the classical IUT III coefficient

  classicalPaperQPilotMagnitude
    = sum_b weight_b * order(qVFamily_b) * log p_b,

i.e. ord_v(q_v) log p_v.  It is NOT c_norm * log p and NOT the normalized
mu_log of qVFamNormalizedNorm.

S154's normalized qPilot object is therefore only a ModelComparison /
Intermediate comparison.  The exact relation of the normalized model to the
classical paper q-pilot is the correction

  actualQPilotMagnitudeClassical
    = classicalPaperQPilotMagnitude + qCorrectionSum,

and equivalently

  globalQPilotLog
    = -classicalPaperQPilotMagnitude - qCorrectionSum.

No target is redefined here.  QVFamNormInstanceGap remains diagnostic only.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S155FrozenTargetStatusActualAdapted

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
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual
open LeanFormal.IUT.XiFPaper.S121QVFamSpectralValuationActual
open LeanFormal.IUT.XiFPaper.S134ActualPaperTargetCorrectionActual
open LeanFormal.IUT.XiFPaper.S137PaperTargetCorrectionStatusActual
open LeanFormal.IUT.XiFPaper.S145NormRatioCorrectionZeroActual
open LeanFormal.IUT.XiFPaper.S154PaperNormalizedQUnitActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S64DependentThetaHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S92NormRatioUnifiedActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Frozen classical paper q-pilot magnitude: ord_v(q_v) log p_v. -/
noncomputable def classicalPaperQPilotMagnitude : Real :=
  paperQPilotCoefficientSum T

/-- Frozen paper q-pilot unfolds exactly to the order log p sum. -/
theorem classicalPaperQPilotMagnitude_eq :
    classicalPaperQPilotMagnitude T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (((qVFamily T b).order : Real) *
            Real.log (qVFamTensorP T b : Real)) :=
  rfl

/-- S154's normalized comparison is only the model comparison. -/
def NormalizedModelComparison : Prop :=
  PaperNormalizedUncorrectedComparison T

/-- The normalized model comparison is not the frozen classical paper target;
it is the actual normalized qPilot inequality from S154. -/
theorem normalizedModelComparison_iff_globalQPilot :
    NormalizedModelComparison T ↔
      qVFamNormalizedQPilotLog T ≤ globalThetaHullLog T :=
  Iff.rfl

/-- Exact gap between the actual qPilot scalar and the frozen classical paper
q-pilot scalar. -/
theorem actualQPilotMagnitude_eq_classicalPaper_add_qCorrection :
    actualQPilotMagnitudeClassical (l := l) T =
      classicalPaperQPilotMagnitude T + qCorrectionSum T := by
  unfold classicalPaperQPilotMagnitude
  rw [actualQPilotMagnitude_eq_s13Q]
  exact s13QPilotCoefficientSum_eq_paper_add_correction T

/-- Equivalent normalized-model form of the exact gap. -/
theorem globalQPilotLog_eq_neg_classicalPaper_sub_qCorrection :
    globalQPilotLog T =
      -classicalPaperQPilotMagnitude T - qCorrectionSum T := by
  have h := actualQPilotMagnitude_eq_classicalPaper_add_qCorrection T
  have hQ : actualQPilotMagnitudeClassical (l := l) T = -globalQPilotLog T := by
    rw [actualQPilotMagnitude_eq_s13Q]
    unfold globalQPilotLog
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _
    unfold perBQPilotLog qPilotClassicalLog
    ring
  linarith

/-- The normalized model qPilot is not silently identified with the frozen
classical paper q-pilot: their difference is exactly qCorrectionSum. -/
theorem normalizedModel_eq_classicalPaper_iff_qCorrection_zero :
    globalQPilotLog T = -classicalPaperQPilotMagnitude T ↔
      qCorrectionSum T = 0 := by
  rw [globalQPilotLog_eq_neg_classicalPaper_sub_qCorrection]
  constructor <;> intro h <;> linarith

end LeanFormal.IUT.XiFPaper.S155FrozenTargetStatusActualAdapted

end
