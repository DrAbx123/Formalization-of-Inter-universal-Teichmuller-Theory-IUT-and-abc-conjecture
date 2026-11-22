import tmp.sheaf.xif.paper.BadPlaceThetaHullCorrectionFormulaActual
import tmp.sheaf.xif.paper.BadPlaceNormRatioCorrectionActual
import tmp.sheaf.xif.paper.BadPlaceRootHullScalingFormulaActual
/-! # Strict paper xi-f target: correction-free
This file deliberately does NOT package the paper-normalized comparison with
a correction as the final paper xi-f theorem.  The strict target requires the
three actual corrections to vanish:
  normRatioCorrectionSum = 0,
  halfNormRatioCorrectionSum = 0,
  thetaHullCoefficientCorrection = 0.
The exact sufficient source fields are recorded (norm ratio one at every bad
place and the root-hull scaling formula at every bad place).  They are not
inhabited here; the strict target remains missing until those fields are built.
No fake correction=0. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.BadPlacePaperTargetStrictActual
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
open LeanFormal.IUT.XiFPaper.BadPlaceThetaHullCorrectionFormulaActual
open LeanFormal.IUT.XiFPaper.BadPlaceRootHullScalingFormulaActual
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
/-- Strict correction-free paper target. -/
def PaperXiFTargetStrict : Prop :=
  normRatioCorrectionSum T = 0 ∧
    halfNormRatioCorrectionSum T = 0 ∧
      thetaHullCoefficientCorrection (l := l) T = 0
/-- Exact sufficient source fields making all three corrections vanish. -/
structure PaperSourceCorrectionFreeFields where
  normRatio_one : ∀ b : Bad (nativePlaceSelection T),
    qVFamNormRatio T b = 1
  rootHull_scaling : ∀ b : Bad (nativePlaceSelection T),
    RootHullScalingFormulaAt T b
/-- The exact source-field condition is not asserted. -/
def PaperCorrectionFreeSourceGap : Prop :=
  Nonempty (PaperSourceCorrectionFreeFields T)
/-- Source fields imply zero norm-ratio correction. -/
theorem normRatioCorrectionSum_eq_zero_of_fields
    (S : PaperSourceCorrectionFreeFields T) :
    normRatioCorrectionSum T = 0 := by
  unfold normRatioCorrectionSum
  apply Finset.sum_eq_zero
  intro b _
  rw [S.normRatio_one b, Real.log_one, mul_zero]
/-- Source fields imply zero half norm-ratio correction. -/
theorem halfNormRatioCorrectionSum_eq_zero_of_fields
    (S : PaperSourceCorrectionFreeFields T) :
    halfNormRatioCorrectionSum T = 0 := by
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  have hnorm := twoL_mul_halfNormRatioCorrectionSum T
  rw [normRatioCorrectionSum_eq_zero_of_fields T S] at hnorm
  exact (mul_eq_zero.mp hnorm).resolve_left htwo
/-- Source fields imply zero Theta-hull coefficient correction. -/
theorem thetaHullCoefficientCorrection_eq_zero_of_fields
    (S : PaperSourceCorrectionFreeFields T) :
    thetaHullCoefficientCorrection (l := l) T = 0 :=
  thetaHullCoefficientCorrection_eq_zero_of_scaling_formula T S.rootHull_scaling
/-- The strict correction-free target follows from the exact source fields. -/
theorem paperXiFTargetStrict_of_fields
    (S : PaperSourceCorrectionFreeFields T) : PaperXiFTargetStrict T := by
  refine ⟨normRatioCorrectionSum_eq_zero_of_fields T S,
    halfNormRatioCorrectionSum_eq_zero_of_fields T S,
    thetaHullCoefficientCorrection_eq_zero_of_fields T S⟩
/-- The strict target is exactly the three vanishing corrections. -/
theorem paperXiFTargetStrict_iff :
    PaperXiFTargetStrict T ↔
      normRatioCorrectionSum T = 0 ∧
        halfNormRatioCorrectionSum T = 0 ∧
          thetaHullCoefficientCorrection (l := l) T = 0 := Iff.rfl
/-- Under the strict target the paper-normalized comparison has no correction. -/
theorem paperNormalizedComparison_exact_of_strict
    (h : PaperXiFTargetStrict T) :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T := by
  rcases h with ⟨hnorm, hhalf, htheta⟩
  have hcorr : paperNormalizedCorrection T = 0 := by
    unfold paperNormalizedCorrection
    rw [hhalf, hnorm, sub_self]
  simpa [hcorr] using paperNormalizedComparison_with_correction T
end LeanFormal.IUT.XiFPaper.BadPlacePaperTargetStrictActual
