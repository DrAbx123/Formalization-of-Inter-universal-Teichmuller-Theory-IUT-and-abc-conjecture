import tmp.sheaf.xif.paper.S692QPilotRegionNormExactActual
import tmp.sheaf.xif.paper.QVPilotClassicalRootContainmentActual
/-! # S697: coefficient/region exact reduction of QPilotRegionNormExactGoal
The concrete qPilotClassicalRegion at c_norm is the root-label region at j=1
(coefficient c_root <= c_norm).  Thus the region norm goal reduces exactly to
the root-label-region norm bound by rootImageRadius; the coefficient comparison
is actual.  No false norm inequality is asserted. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S697QPilotRegionCoefficientReductionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.S671QPilotRadiusAuditActual
open LeanFormal.IUT.XiFPaper.S687QPilotSourceNormBoundActual
open LeanFormal.IUT.XiFPaper.S692QPilotRegionNormExactActual
open LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Concrete specialization cNorm = c_norm of the qPilot classical coefficient. -/
noncomputable def qPilotClassicalNormGoal : Prop :=
  QPilotRegionNormExactGoal (l := l) T b
    (fun _ : qVFamTensorV => qVFamTensorCoefficient T b)
/-- Root-label region norm bound at j=1. -/
def RootLabelRegionNormLeRootRadius : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotRootLabelRegion T b (oneSignedLabel (l := l)) →
      ‖x‖ ≤ (rootImageRadius T b : Real)
/-- Actual coefficient comparison c_root <= c_norm. -/
theorem qPilotRootCoefficient_le_classical_actual :
    ∀ i : qVFamTensorV,
      qPilotRootCoefficient T b i ≤ qPilotClassicalCoefficient T b i :=
  qPilotRootCoefficient_le_classical T b
/-- Exact reduction: the concrete qPilot region norm goal follows from the
root-label-region norm bound. -/
theorem qPilotClassicalNormGoal_of_rootLabelRegion
    (h : RootLabelRegionNormLeRootRadius (l := l) T b) :
    qPilotClassicalNormGoal (l := l) T b := by
  intro x hx
  have hc : LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual.qPilotClassicalCoefficient T b =
      (fun _ : qVFamTensorV => qVFamTensorCoefficient T b) := rfl
  have hx' : x ∈ qPilotClassicalRegion T b := by
    simpa [hc, LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual.qPilotClassicalRegion,
      LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual.qPilotClassicalRegion,
      LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual.qPilotClassicalCoefficient,
      thetaTensorScaledRegion] using hx
  exact h x (qPilotClassicalRegion_subset_rootLabelRegion_one T b hx')
/-- Exact remaining goal in coefficient/region form. -/
def S697ExactGoal : Prop :=
  RootLabelRegionNormLeRootRadius (l := l) T b
end LeanFormal.IUT.XiFPaper.S697QPilotRegionCoefficientReductionActual
