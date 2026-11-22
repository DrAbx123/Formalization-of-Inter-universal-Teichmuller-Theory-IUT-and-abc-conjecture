import tmp.sheaf.xif.paper.S2744PerPlaceRegionAllCoordsActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2801RegionAllMonotoneActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2744PerPlaceRegionAllCoordsActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]
variable [∀ i, NeZero (Module.finrank ℚ_[p] (M i))]
variable [DecidableEq ι]

theorem regionAll_mono
    {rho sigma : ι → ℝ} (h : ∀ i, rho i ≤ sigma i) :
    S2726PerPlaceUpdateRegionAll (p := p) M rho
      ⊆ S2726PerPlaceUpdateRegionAll (p := p) M sigma := by
  intro y hy
  rw [S2726PerPlaceUpdateRegionAll, Set.mem_preimage] at hy ⊢
  intro x
  exact (hy x).trans (Finset.sum_le_sum (fun i _ => h i))

#check regionAll_mono
end LeanFormal.IUT.XiFPaper.S2801RegionAllMonotoneActual
end
