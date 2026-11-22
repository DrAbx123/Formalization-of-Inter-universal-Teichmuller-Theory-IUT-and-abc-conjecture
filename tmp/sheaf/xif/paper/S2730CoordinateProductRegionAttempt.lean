import Mathlib
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

noncomputable section
open scoped TensorProduct
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor

namespace LeanFormal.IUT.XiFPaper.S2730CoordinateProductRegionAttempt

universe u

variable {p : Nat} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type u) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]
variable (rho : ι → Real)

/-- Local region: coordinates k at place i bounded by rho i. -/
def localRegion (i : ι) : Set (Fin (Module.finrank ℚ_[p] (M i)) → ℚ_[p]) :=
  { t | ∀ k, Real.log ‖t k‖ ≤ rho i }

/-- Product region with per-coordinate radii R : Index → ℝ. -/
def coordinateBallRegion
    (R : FinitePadicTensorIndex (p := p) M → Real) :
    Set (FinitePadicTensor (p := p) M) :=
  (finitePadicTensorCoordinates (p := p) M) ⁻¹'
    Set.pi Set.univ
      (fun j => { t : ℚ_[p] | Real.log ‖t‖ ≤ R j })

#check coordinateBallRegion
end LeanFormal.IUT.XiFPaper.S2730CoordinateProductRegionAttempt
end
