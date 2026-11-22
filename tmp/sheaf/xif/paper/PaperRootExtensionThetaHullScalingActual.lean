import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual

/-! # Scaling comparison for the actual root image hull -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The image hull is a coordinatewise scaled product of unit balls. -/
def IsCoordinatewiseScaledHull
    (S : Set (RootExtensionProductCarrier T)) : Prop :=
  ∃ r : Bad (nativePlaceSelection T) → NNReal,
    S = Set.pi Set.univ (fun b =>
      Metric.closedBall (0 : rootNormedExtension T b) ((r b : NNReal) : Real))

/-- The image hull is the coordinatewise lambda-O hull with lambda b = rootImageRadius b. -/
theorem rootExtensionProductImageHull_is_scaledHull :
    IsCoordinatewiseScaledHull T (rootExtensionProductImageHull T) :=
  ⟨rootImageRadius T, rfl⟩

/-- Minimality: any coordinatewise scaled closed-ball hull containing the image
has radii at least the image radius. -/
theorem rootExtensionProductImageHull_subset_scaledHull
    (r : Bad (nativePlaceSelection T) → NNReal)
    (hr : ∀ b, rootImageRadius T b ≤ r b) :
    rootExtensionProductImageHull T ⊆
      Set.pi Set.univ (fun b =>
        Metric.closedBall (0 : rootNormedExtension T b) ((r b : NNReal) : Real)) := by
  intro x hx b hb
  have hx' : (x b : rootNormedExtension T b) ∈
      Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real) := hx b hb
  rw [Metric.mem_closedBall] at hx' ⊢
  exact hx'.trans (by exact_mod_cast hr b)

/-- Uniform scaling radius: the largest coordinate image radius. -/
noncomputable def rootImageUniformRadius : NNReal :=
  Finset.univ.sup (fun b : Bad (nativePlaceSelection T) => rootImageRadius T b)

/-- Uniformly scaled product hull (single lambda applied to every coordinate). -/
def rootExtensionProductUniformImageHull :
    Set (RootExtensionProductCarrier T) :=
  Set.pi Set.univ (fun b =>
    Metric.closedBall (0 : rootNormedExtension T b)
      ((rootImageUniformRadius T : NNReal) : Real))

/-- The coordinatewise image hull is contained in the uniform scaled hull. -/
theorem rootExtensionProductImageHull_subset_uniform :
    rootExtensionProductImageHull T ⊆ rootExtensionProductUniformImageHull T := by
  apply rootExtensionProductImageHull_subset_scaledHull
  intro b
  unfold rootImageUniformRadius
  exact Finset.le_sup (α := NNReal) (β := Bad (nativePlaceSelection T))
    (s := Finset.univ)
    (f := fun b : Bad (nativePlaceSelection T) => rootImageRadius T b)
    (b := b) (Finset.mem_univ b)

/-- Exact gap condition for uniform scaling. -/
def RootImageUniformScalingGap : Prop :=
  ∃ b : Bad (nativePlaceSelection T), rootImageRadius T b < rootImageUniformRadius T

/-- If every coordinate has the same radius, the coordinatewise image hull is
the uniform scaled hull. -/
theorem rootExtensionProductImageHull_eq_uniform_of_radii_eq
    (h : ∀ b : Bad (nativePlaceSelection T),
      rootImageRadius T b = rootImageUniformRadius T) :
    rootExtensionProductImageHull T = rootExtensionProductUniformImageHull T := by
  apply Set.Subset.antisymm
  · exact rootExtensionProductImageHull_subset_uniform T
  · intro x hx b hb
    have hx' : (x b : rootNormedExtension T b) ∈
        Metric.closedBall (0 : rootNormedExtension T b)
          ((rootImageUniformRadius T : NNReal) : Real) := hx b hb
    rw [Metric.mem_closedBall] at hx' ⊢
    rw [h b]
    exact hx'

end LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullScalingActual

end