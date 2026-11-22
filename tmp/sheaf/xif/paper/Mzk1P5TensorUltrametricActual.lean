import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRegion
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Analysis.Normed.Field.Ultra
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P5TensorUltrametricActual
open LeanFormal.IUT.LocalFieldPadicTensor
/-- Coordinate pullback of the finite p-adic tensor norm is nonarchimedean. -/
theorem finitePadicTensor_isUltrametric
    {p : Nat} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
    [∀ i, NormedSpace ℚ_[p] (M i)] [∀ i, FiniteDimensional ℚ_[p] (M i)]
    [∀ i, IsUltrametricDist (M i)] :
    IsUltrametricDist (FinitePadicTensor (p := p) M) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm ?_
  intro x y
  change ‖finitePadicTensorCoordinates (p := p) M (x + y)‖ ≤
    max ‖finitePadicTensorCoordinates (p := p) M x‖
      ‖finitePadicTensorCoordinates (p := p) M y‖
  rw [map_add]
  exact IsUltrametricDist.norm_add_le_max _ _
#check finitePadicTensor_isUltrametric
end LeanFormal.IUT.XiFPaper.Mzk1P5TensorUltrametricActual
end