import tmp.sheaf.xif.paper.S2744PerPlaceRegionAllCoordsActual
import tmp.sheaf.xif.paper.S2736cTensorLatticeActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2797TensorLatticeSubsetAllRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2744PerPlaceRegionAllCoordsActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]
variable [∀ i, NeZero (Module.finrank ℚ_[p] (M i))]
variable [DecidableEq ι]

theorem tensorLattice_subset_regionAll
    (rho : ι → ℝ) (hρ : ∀ i, 0 ≤ rho i) :
    tensorLattice (p := p) M ⊆ S2726PerPlaceUpdateRegionAll (p := p) M rho := by
  intro x hx
  rw [S2726PerPlaceUpdateRegionAll, Set.mem_preimage]
  rcases ((tensorLattice_mem_iff (p := p) (M := M) x).mp hx) with ⟨z, hz⟩
  refine log_le_sum_of_norm_le_one (p := p) (ι := ι) (M := M) rho hρ
    (finitePadicTensorCoordinates (p := p) M x) ?_
  intro j
  rw [← hz]
  exact (z j).2

#check tensorLattice_subset_regionAll
end LeanFormal.IUT.XiFPaper.S2797TensorLatticeSubsetAllRegionActual
end
