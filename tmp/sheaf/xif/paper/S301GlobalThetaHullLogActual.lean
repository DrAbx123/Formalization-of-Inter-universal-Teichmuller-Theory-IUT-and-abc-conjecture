import tmp.sheaf.xif.paper.S294SourceHullNormalizedLogActual

/-!
# S301: global weighted Theta-hull log and s13/root normalization

The per-b corrected source hull log-volume from S294 is weighted by the actual
nativeBadLocalWeight and summed over the bad places.  The same weighted sums of
the s13 root coefficient and the 2l-multiple tensor coefficient are constructed,
with their exact normalization identities.  Theta-label coefficients are also
weighted and identified with j^2 times the global root coefficient.

Only objects/formulas are built; no inequality is asserted.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S301GlobalThetaHullLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S294SourceHullNormalizedLogActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Global weighted corrected-hull normalized log-volume. -/
noncomputable def globalSourceHullNormalizedLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      sourceQTensorHullNormalizedLog T b

/-- Exact weighted log-mass formula for the global normalized log. -/
theorem globalSourceHullNormalizedLog_eq :
    globalSourceHullNormalizedLog T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (Real.log (sourceQTensorHullMass T b).toReal -
            Real.log (sourceQTensorUnitReferenceMass T b).toReal) := by
  unfold globalSourceHullNormalizedLog
  apply Finset.sum_congr rfl
  intro b _
  rw [sourceQTensorHullNormalizedLog_eq_log_sub_log T b]

/-- Global weighted s13 root coefficient order/(2l). -/
noncomputable def globalSourceHullS13RootCoefficient : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * qVFamPaperRootCoefficient T b

/-- Global weighted s13 tensor coefficient 2l * root. -/
noncomputable def globalSourceHullS13TensorCoefficient : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * qVFamTensorCoefficient T b

/-- The global tensor coefficient is exactly 2l times the global root
coefficient. -/
theorem globalSourceHullS13TensorCoefficient_eq_twoL_mul_root :
    globalSourceHullS13TensorCoefficient T =
      (2 * l.value : Real) * globalSourceHullS13RootCoefficient T := by
  unfold globalSourceHullS13TensorCoefficient
    globalSourceHullS13RootCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [qVFamTensorCoefficient_eq_twoL_mul_rootCoefficient T b]
  ring

/-- Exact order formula for the global root coefficient. -/
theorem globalSourceHullS13RootCoefficient_eq_order_sum :
    globalSourceHullS13RootCoefficient T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (((qVFamily T b).order : Real) / (2 * l.value : Real)) := by
  unfold globalSourceHullS13RootCoefficient
  apply Finset.sum_congr rfl
  intro b _
  rw [qVFamPaperRootCoefficient]

/-- Global weighted paper theta tensor coefficient at label j. -/
noncomputable def globalSourceHullThetaCoefficient
    (j : SignedLabel l.value) : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * qVFamPaperThetaTensorCoefficient T b j

/-- Exact j^2 normalization of the global theta coefficient. -/
theorem globalSourceHullThetaCoefficient_eq_j2_mul_root
    (j : SignedLabel l.value) :
    globalSourceHullThetaCoefficient T j =
      ((gaussExponent j.1).toNat : Real) *
        globalSourceHullS13RootCoefficient T := by
  unfold globalSourceHullThetaCoefficient
    globalSourceHullS13RootCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [qVFamPaperThetaTensorCoefficient]
  ring

/-- Actual global weighted theta-log + root normalization object. -/
structure GlobalSourceThetaHullLogObject where
  weightedNormalizedLog : Real
  weightedNormalizedLog_eq :
    weightedNormalizedLog = globalSourceHullNormalizedLog T
  weightedNormalizedLog_formula :
    weightedNormalizedLog =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (Real.log (sourceQTensorHullMass T b).toReal -
            Real.log (sourceQTensorUnitReferenceMass T b).toReal)
  weightedRootCoefficient : Real
  weightedRootCoefficient_eq :
    weightedRootCoefficient = globalSourceHullS13RootCoefficient T
  weightedTensorCoefficient : Real
  weightedTensorCoefficient_eq :
    weightedTensorCoefficient = globalSourceHullS13TensorCoefficient T
  tensor_eq_twoL_mul_root :
    weightedTensorCoefficient = (2 * l.value : Real) * weightedRootCoefficient
  thetaCoefficient : SignedLabel l.value -> Real
  thetaCoefficient_eq :
    thetaCoefficient = globalSourceHullThetaCoefficient T
  thetaCoefficient_j2 :
    ∀ j : SignedLabel l.value,
      thetaCoefficient j =
        ((gaussExponent j.1).toNat : Real) * weightedRootCoefficient

/-- Actual global weighted theta-log/root object constructor. -/
noncomputable def globalSourceThetaHullLogObject :
    GlobalSourceThetaHullLogObject T where
  weightedNormalizedLog := globalSourceHullNormalizedLog T
  weightedNormalizedLog_eq := rfl
  weightedNormalizedLog_formula := globalSourceHullNormalizedLog_eq T
  weightedRootCoefficient := globalSourceHullS13RootCoefficient T
  weightedRootCoefficient_eq := rfl
  weightedTensorCoefficient := globalSourceHullS13TensorCoefficient T
  weightedTensorCoefficient_eq := rfl
  tensor_eq_twoL_mul_root :=
    globalSourceHullS13TensorCoefficient_eq_twoL_mul_root T
  thetaCoefficient := globalSourceHullThetaCoefficient T
  thetaCoefficient_eq := rfl
  thetaCoefficient_j2 :=
    globalSourceHullThetaCoefficient_eq_j2_mul_root T

end LeanFormal.IUT.XiFPaper.S301GlobalThetaHullLogActual

end
