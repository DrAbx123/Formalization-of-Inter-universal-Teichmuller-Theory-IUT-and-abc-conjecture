import tmp.sheaf.xif.paper.S876CorrectedGlobalTargetActual
import tmp.sheaf.xif.paper.S825StackFactorCNormEquivActual
import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.S820FiniteLScalingGeneratorActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S877WeightedIdentificationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S876CorrectedGlobalTargetActual
open LeanFormal.IUT.XiFPaper.S825StackFactorCNormEquivActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.S820FiniteLScalingGeneratorActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Corrected hq: the classical q-pilot must be multiplied by 2l to compare with
the paper order/(2l) least-hull scalar. -/
def HqCorrected : Prop :=
  S860GlobalCor312AuditActual.weightedQPilot T =
    (2 * (l.value : Real)) * paperQPilotWeightedLeast T

/-- Corrected htheta: 2l times the hull scalar equals the least-hull scalar. -/
def HthetaCorrected : Prop :=
  (2 * (l.value : Real)) * S860GlobalCor312AuditActual.thetaHullScalar T =
    paperLeastHullWeightedLog T

/-- Paper q-pilot least-hull scalar is nonpositive. -/
theorem paperQPilotWeightedLeast_nonpos :
    paperQPilotWeightedLeast T ≤ 0 := by
  unfold paperQPilotWeightedLeast paperQPilotLogLeast
  apply Finset.sum_nonpos
  intro b _
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact nativeBadLocalWeight_nonneg T b
  · unfold paperRootCoefficientFamily qVFamPaperRootCoefficient
    have hsum : 0 <= ∑ _ : qVFamTensorV,
        ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := by
      apply Finset.sum_nonneg
      intro _ _
      positivity
    have hp : (0 : Real) < Real.log (qVFamTensorP T b : Real) := by
      have h1 : (1 : Real) < (qVFamTensorP T b : Real) := by
        exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
      exact Real.log_pos h1
    have := mul_nonneg hsum hp.le
    nlinarith [this]

theorem correctedGlobalTarget_of_corrected_identifications
    (hdata : ∀ b : Bad (nativePlaceSelection T), PaperLeastHullData T b)
    (hq : HqCorrected T) (htheta : HthetaCorrected T) :
    CorrectedGlobalTarget T := by
  unfold CorrectedGlobalTarget
  rw [hq, htheta]
  rw [paperQPilotWeightedLeast_eq_leastHullWeighted T hdata]
  have hnp := paperQPilotWeightedLeast_nonpos T
  have hleast : paperLeastHullWeightedLog T ≤ 0 := by
    rw [← paperQPilotWeightedLeast_eq_leastHullWeighted T hdata]
    exact hnp
  have h2 : (1 : Real) <= 2 * (l.value : Real) := by
    have := l.ge_five
    have : (5 : Real) <= (l.value : Real) := by exact_mod_cast this
    nlinarith
  nlinarith

/-- Actual S817/S825 weighted norm bridge: every per-b factor is one iff
c_norm = order at every b. -/
theorem weightedNormBridge_iff_cNorm_eq_order :
    (∀ b : Bad (nativePlaceSelection T),
      StackRootUnitFactorOne T b) ↔
      ∀ b : Bad (nativePlaceSelection T),
        qVFamNormalizedCoefficient (l := l) T b = ((qVFamily T b).order : Real) := by
  constructor
  · intro h b
    exact (StackRootUnitFactorOne_iff_cNorm_eq_order (l := l) T b).mp (h b)
  · intro h b
    exact (StackRootUnitFactorOne_iff_cNorm_eq_order (l := l) T b).mpr (h b)

/-- Exact minimal gap left by S877: corrected hq and htheta. -/
def CorrectedHqHthetaGap : Prop :=
  HqCorrected T ∧ HthetaCorrected T

end LeanFormal.IUT.XiFPaper.S877WeightedIdentificationActual
end