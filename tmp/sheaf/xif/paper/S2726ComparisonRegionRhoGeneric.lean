import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2726ComparisonRegionRhoGeneric
variable {ι : Type*} {F : ι → Type*} [∀ i, Norm (F i)]
def comparisonRegionRhoUpper (rho : ι → ℝ) : Set ((i : ι) → F i) :=
  { x | ∀ i, Real.log ‖x i‖ ≤ rho i }
def comparisonRegionRho (rho : ι → ℝ) : Set ((i : ι) → F i) :=
  { x | ∀ i, -rho i ≤ Real.log ‖x i‖ ∧ Real.log ‖x i‖ ≤ rho i }
#check comparisonRegionRhoUpper
end LeanFormal.IUT.XiFPaper.S2726ComparisonRegionRhoGeneric
end
