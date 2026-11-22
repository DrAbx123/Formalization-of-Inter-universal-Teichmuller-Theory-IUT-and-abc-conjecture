import tmp.sheaf.xif.paper.QVPilotClassicalRootContainmentActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S673QPilotRootImageContainmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The q-pilot classical image under the actual block linear equivalence. -/
noncomputable def qPilotImageInRootExtension : Set (rootNormedExtension T b) :=
  blockLinearEquiv T b '' qPilotClassicalRegion T b

/-- The per-b root image coordinate: the closed ball of radius rootImageRadius. -/
noncomputable def rootImageCoordinate : Set (rootNormedExtension T b) :=
  Metric.closedBall (0 : rootNormedExtension T b)
    ((rootImageRadius T b : NNReal) : Real)

/-- Exact norm bound needed for the containment. -/
def QPilotClassicalRegionNormBound : Prop :=
  ∀ x ∈ qPilotClassicalRegion T b,
    ‖blockLinearEquiv T b x‖ ≤ (rootImageRadius T b : Real)

theorem qPilotImageInRootExtension_subset_rootImageCoordinate
    (h : QPilotClassicalRegionNormBound T b) :
    qPilotImageInRootExtension T b ⊆ rootImageCoordinate T b := by
  rintro y ⟨x, hx, rfl⟩
  rw [rootImageCoordinate, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact h x hx

/-- Exact minimal gap for the containment. -/
def QPilotRootImageContainmentGap : Prop :=
  QPilotClassicalRegionNormBound T b

end LeanFormal.IUT.XiFPaper.S673QPilotRootImageContainmentActual

end
