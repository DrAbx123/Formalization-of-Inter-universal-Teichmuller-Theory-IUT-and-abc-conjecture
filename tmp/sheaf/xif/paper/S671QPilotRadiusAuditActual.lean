import tmp.sheaf.xif.paper.S668QPilotRootExtensionPerBActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual

/-! # S671: audit of the per-b containment via the radius relation

The qPilot image lies in the canonical root image closure iff the norm of the
actual per-b image is bounded by `rootImageRadius`.  This is the exact radius
gap between `qPilotClassicalRegion` and `rootExtensionProductImageHull`.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S671QPilotRadiusAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (cNorm : qVFamTensorV → Real)
variable (dataNorm : ArithmeticTuplePureFractionalScalingData
  (qVFamTensorPlaces T b) qVFamTensorTuple cNorm)

/-- The product-coordinate projection of the image hull is exactly the closed
ball of radius `rootImageRadius`. -/
theorem rootImageCoordinate_eq_closedBall :
    rootImageCoordinate (l := l) T b =
      Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real) := by
  classical
  ext y
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf b (Set.mem_univ b)
  · intro hy
    let f : RootExtensionProductCarrier T :=
      Function.update (fun b' => (0 : rootNormedExtension T b')) b y
    refine ⟨f, ?_, ?_⟩
    · intro b' _
      by_cases h : b' = b
      · subst h
        simpa [f] using hy
      · have hzero : (0 : rootNormedExtension T b') ∈
            Metric.closedBall (0 : rootNormedExtension T b')
              ((rootImageRadius T b' : NNReal) : Real) := by
          rw [Metric.mem_closedBall]
          simp
        simpa [f, h] using hzero
    · change (Function.update (fun b' => (0 : rootNormedExtension T b')) b y) b = y
      simp

/-- Exact radius condition for the per-b containment. -/
def QPilotRadiusBoundObstacle : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple cNorm →
      ‖qPilotToRootExtension (l := l) T b x‖ ≤ (rootImageRadius T b : Real)

/-- Containment is equivalent to the pointwise norm-radius bound. -/
theorem perBContainment_iff_radiusBound :
    QPilotPerBContainmentObstacle (l := l) T b cNorm ↔
      QPilotRadiusBoundObstacle (l := l) T b cNorm := by
  unfold QPilotPerBContainmentObstacle QPilotRadiusBoundObstacle
  rw [rootImageCoordinate_eq_closedBall]
  constructor
  · intro h x hx
    have hmem : qPilotToRootExtension (l := l) T b x ∈
        qPilotImageInRootExtension (l := l) T b cNorm := ⟨x, hx, rfl⟩
    have hball := h hmem
    rw [Metric.mem_closedBall] at hball
    simpa [dist_eq_norm] using hball
  · rintro h y ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall]
    simpa [dist_eq_norm] using h x hx

/-- Conditional per-b containment from the exact radius bound. -/
theorem perBContainment_of_radiusBound
    (h : QPilotRadiusBoundObstacle (l := l) T b cNorm) :
    QPilotPerBContainmentObstacle (l := l) T b cNorm :=
  (perBContainment_iff_radiusBound (l := l) T b cNorm).mpr h

/-- Exact radius gap: no pointwise norm bound is currently proved in the
tree; the qPilot region is a fractional-lattice scaled region, while the root
image coordinate is a closed ball of root-theta radius. -/
def QPilotRadiusBoundRequired : Prop :=
  QPilotRadiusBoundObstacle (l := l) T b cNorm

end LeanFormal.IUT.XiFPaper.S671QPilotRadiusAuditActual
end
