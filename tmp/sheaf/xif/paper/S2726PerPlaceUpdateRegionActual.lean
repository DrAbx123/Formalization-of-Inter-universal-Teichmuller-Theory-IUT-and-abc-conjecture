import Mathlib
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

noncomputable section
open scoped TensorProduct
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor

namespace LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual

universe u

variable {p : Nat} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type u) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]
variable [∀ i, NeZero (Module.finrank ℚ_[p] (M i))]
variable [DecidableEq ι]

/-- Default tensor coordinate. -/
def defaultTensorIndex : FinitePadicTensorIndex (p := p) M :=
  fun i => ⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℚ_[p] (M i)))⟩

/-- Per-place region: at each place i, only the coordinate with i-th entry k is bounded. -/
def S2726PerPlaceUpdateRegion
    (rho : ι → Real) : Set (FinitePadicTensor (p := p) M) :=
  (finitePadicTensorCoordinates (p := p) M) ⁻¹'
    { y | ∀ (i : ι) (k : Fin (Module.finrank ℚ_[p] (M i))),
        Real.log ‖y (Function.update (defaultTensorIndex (p := p) M) i k)‖ ≤ rho i }

/-- Exact requested name. -/
def S2726PerPlaceRegionDefault
    (rho : ι → Real) : Set (FinitePadicTensor (p := p) M) :=
  S2726PerPlaceUpdateRegion (p := p) M rho

#check S2726PerPlaceRegionDefault
#check S2726PerPlaceUpdateRegion
end LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
end
