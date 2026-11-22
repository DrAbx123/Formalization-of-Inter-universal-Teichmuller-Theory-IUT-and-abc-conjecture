import tmp.sheaf.xif.paper.S668QPilotRootExtensionPerBActual
/-! # S670: reduction of QPilotPerBContainmentObstacle to the pointwise norm bound
The product image hull is the coordinatewise closedBall of radius rootImageRadius, so
qPilotImageInRootExtension subset rootImageCoordinate is equivalent to the exact
pointwise norm bound for x in qPilotClassicalRegion.  The latter is the concrete
remaining goal; no containment is fabricated. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S670QPilotRootExtensionContainmentActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (cNorm : qVFamTensorV → Real)
variable (dataNorm : ArithmeticTuplePureFractionalScalingData
  (qVFamTensorPlaces T b) qVFamTensorTuple cNorm)
/-- Exact remaining pointwise goal: the image of the qPilot classical region has
coordinate norm at most rootImageRadius. -/
def QPilotPerBPointwiseNormBound : Prop :=
  ∀ x ∈ qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple cNorm,
    ‖qPilotToRootExtension (l := l) T b x‖ ≤ (rootImageRadius T b : Real)
/-- The per-b containment is exactly the pointwise norm bound. -/
theorem qPilotPerBContainmentObstacle_iff_pointwise :
    QPilotPerBContainmentObstacle (l := l) T b cNorm ↔
      QPilotPerBPointwiseNormBound (l := l) T b cNorm := by
  classical
  constructor
  · intro h x hx
    have hy : qPilotToRootExtension (l := l) T b x ∈
        rootImageCoordinate (l := l) T b :=
      h ⟨x, hx, rfl⟩
    rcases hy with ⟨f, hf, hfb⟩
    rw [← hfb]
    change ‖f b‖ ≤ (rootImageRadius T b : Real)
    have hb := hf b (Set.mem_univ b)
    rw [Metric.mem_closedBall, dist_eq_norm] at hb
    simpa using hb
  · intro h y hy
    rcases hy with ⟨x, hx, rfl⟩
    unfold rootImageCoordinate
    refine ⟨Function.update (fun b' : Bad (nativePlaceSelection T) =>
      (0 : rootNormedExtension T b')) b
        (qPilotToRootExtension (l := l) T b x), ?_, ?_⟩
    · intro b' _
      by_cases hb : b' = b
      · subst hb
        simp [Function.update, Metric.mem_closedBall, dist_eq_norm]
        simpa using h x hx
      · simp [Function.update, hb]
    · simp only [rootExtensionProductCoordinate, Function.update_self]
/-- Actual containment from the pointwise norm bound. -/
theorem qPilotPerBContainmentObstacle_of_pointwise
    (h : QPilotPerBPointwiseNormBound (l := l) T b cNorm) :
    QPilotPerBContainmentObstacle (l := l) T b cNorm :=
  (qPilotPerBContainmentObstacle_iff_pointwise (l := l) T b cNorm).2 h
/-- The exact pointwise goal is the only remaining assertion; it is recorded
as a Prop, not proved by changing the target. -/
def S670ExactPointwiseGoal : Prop :=
  QPilotPerBPointwiseNormBound (l := l) T b cNorm
end LeanFormal.IUT.XiFPaper.S670QPilotRootExtensionContainmentActual
