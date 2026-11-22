import tmp.sheaf.xif.paper.S668QPilotRootExtensionPerBActual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import tmp.sheaf.xif.paper.S671QPilotRadiusAuditActual

/-! # S678: Mathlib finite-dimensional operator bound for the per-b qPilot map

Mathlib provides:
* `LinearMap.continuous_of_finiteDimensional`
  (Mathlib/Topology/Algebra/Module/FiniteDimension.lean): every linear map from
  a finite-dimensional Hausdorff TVS over a complete field is continuous;
* `SemilinearMapClass.bound_of_continuous`
  (Mathlib/Analysis/Normed/Operator/Basic.lean): a continuous (semi)linear map
  has a positive multiplicative norm bound.
Here qVFamTensorBlock is a finite-dimensional normed Qp-space (FinitePadicTensor),
and rootNormedExtension is finite-dimensional normed over Qp, so both apply.
The remaining gap is only the source-region norm bound.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S678QPilotRootExtensionOperatorBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S671QPilotRadiusAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S671QPilotRadiusAuditActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (cNorm : qVFamTensorV → Real)
variable (dataNorm : ArithmeticTuplePureFractionalScalingData
  (qVFamTensorPlaces T b) qVFamTensorTuple cNorm)
variable [ContinuousSMul ℚ_[qVFamTensorP T b] (rootNormedExtension T b)]

/-- The linear map underlying the actual per-b qPilot map. -/
noncomputable def qPilotBlockLinearMap :
    qVFamTensorBlock T b →ₗ[ℚ_[qVFamTensorP T b]] rootNormedExtension T b where
  toFun x :=
    algebraMap (rootBase T b) (rootNormedExtension T b)
      (qVFamBlockLinearEquiv (l := l) T b x)
  map_add' x y := by
    simp [map_add]
  map_smul' c x := by
    simp only [LinearEquiv.map_smul]
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    rw [← IsScalarTower.algebraMap_apply (R := ℚ_[qVFamTensorP T b])
      (S := rootBase T b) (A := rootNormedExtension T b) c]
    simp

theorem qPilotBlockLinearMap_apply (x : qVFamTensorBlock T b) :
    qPilotBlockLinearMap (l := l) T b x =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        (qVFamBlockLinearEquiv (l := l) T b x) :=
  rfl

theorem qPilotToRootExtension_eq_linearMap (x : qVFamTensorBlock T b) :
    qPilotToRootExtension (l := l) T b x =
      qPilotBlockLinearMap (l := l) T b x := by
  simp [qPilotToRootExtension, qPilotBlockToRootTensor,
    qPilotBlockLinearMap, LinearEquiv.apply_symm_apply]

/-- Mathlib finite-dimensional operator bound: the actual per-b qPilot map has
a positive norm bound. -/
theorem qPilotToRootExtension_exists_norm_bound :
    ∃ C : Real, 0 < C ∧
      ∀ x : qVFamTensorBlock T b,
        ‖qPilotToRootExtension (l := l) T b x‖ ≤ C * ‖x‖ := by
  have hcont : Continuous (qPilotBlockLinearMap (l := l) T b) :=
    LinearMap.continuous_of_finiteDimensional (qPilotBlockLinearMap (l := l) T b)
  obtain ⟨C, hCpos, hC⟩ := SemilinearMapClass.bound_of_continuous
    (qPilotBlockLinearMap (l := l) T b) hcont
  refine ⟨C, hCpos, fun x => ?_⟩
  rw [qPilotToRootExtension_eq_linearMap]
  exact hC x

/-- The remaining source-region norm bound for a chosen operator constant. -/
def QPilotSourceNormBound (C : Real) : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple cNorm →
      C * ‖x‖ ≤ (rootImageRadius T b : Real)

/-- Conditional radius bound from a Mathlib operator bound and the source-region
norm bound. -/
theorem qPilotRadiusBound_of_operatorBound
    (C : Real) (hCpos : 0 < C)
    (hCbound : ∀ x : qVFamTensorBlock T b,
      ‖qPilotToRootExtension (l := l) T b x‖ ≤ C * ‖x‖)
    (hsource : QPilotSourceNormBound (l := l) T b cNorm C) :
    QPilotRadiusBoundObstacle T b cNorm := by
  unfold QPilotRadiusBoundObstacle
  intro x hx
  exact le_trans (hCbound x) (hsource x hx)

/-- Exact remaining source norm datum. -/
def QPilotSourceNormBoundRequired : Prop :=
  ∃ C : Real, 0 < C ∧ QPilotSourceNormBound (l := l) T b cNorm C

end LeanFormal.IUT.XiFPaper.S678QPilotRootExtensionOperatorBoundActual
end
