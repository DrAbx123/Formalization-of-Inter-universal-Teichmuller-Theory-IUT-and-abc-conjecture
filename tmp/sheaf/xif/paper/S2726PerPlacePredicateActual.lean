import Mathlib
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

noncomputable section
open scoped TensorProduct
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor

namespace LeanFormal.IUT.XiFPaper.S2726PerPlacePredicateActual

universe u

/-- Per-place radii bound on every tensor coordinate. -/
def S2726PerPlaceRegion
    {p : Nat} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (M : ι → Type u) [∀ i, NormedAddCommGroup (M i)]
    [∀ i, NormedSpace ℚ_[p] (M i)]
    [∀ i, FiniteDimensional ℚ_[p] (M i)]
    (rho : ι → Real) : Set (FinitePadicTensor (p := p) M) :=
  (finitePadicTensorCoordinates (p := p) M) ⁻¹'
    { y | ∀ (j : FinitePadicTensorIndex (p := p) M) (i : ι),
        Real.log ‖y j‖ ≤ rho i }

#check S2726PerPlaceRegion
end LeanFormal.IUT.XiFPaper.S2726PerPlacePredicateActual
end
