import Mathlib
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

noncomputable section
open scoped TensorProduct
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor

namespace LeanFormal.IUT.XiFPaper.S2726TensorComparisonRegionRhoActual

universe u

/-- Tensor-block upper comparison region. -/
def S2726TensorComparisonRegionRhoUpper
    {p : Nat} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (M : ι → Type u) [∀ i, NormedAddCommGroup (M i)]
    [∀ i, NormedSpace ℚ_[p] (M i)]
    [∀ i, FiniteDimensional ℚ_[p] (M i)]
    (rho : FinitePadicTensorIndex (p := p) M → Real) :
    Set (FinitePadicTensor (p := p) M) :=
  (finitePadicTensorCoordinates (p := p) M) ⁻¹'
    { y | ∀ j, Real.log ‖y j‖ ≤ rho j }

/-- Two-sided tensor-block comparison region. -/
def S2726TensorComparisonRegionRho
    {p : Nat} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (M : ι → Type u) [∀ i, NormedAddCommGroup (M i)]
    [∀ i, NormedSpace ℚ_[p] (M i)]
    [∀ i, FiniteDimensional ℚ_[p] (M i)]
    (rho : FinitePadicTensorIndex (p := p) M → Real) :
    Set (FinitePadicTensor (p := p) M) :=
  (finitePadicTensorCoordinates (p := p) M) ⁻¹'
    { y | ∀ j, -rho j ≤ Real.log ‖y j‖ ∧ Real.log ‖y j‖ ≤ rho j }

#check S2726TensorComparisonRegionRhoUpper
#check S2726TensorComparisonRegionRho

end LeanFormal.IUT.XiFPaper.S2726TensorComparisonRegionRhoActual
end
