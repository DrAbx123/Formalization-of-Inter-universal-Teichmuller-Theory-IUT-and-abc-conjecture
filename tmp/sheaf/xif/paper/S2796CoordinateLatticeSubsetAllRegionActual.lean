import tmp.sheaf.xif.paper.S2734LatticeActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2796CoordinateLatticeSubsetAllRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.PadicIntegerProductLattice

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]

theorem coordinateLattice_subset_regionAll
    (rho : ι → ℝ) (hρ : ∀ i, 0 ≤ rho i) :
    padicIntegerCoordinateLattice (p := p) (ι := ι)
      ⊆ {y | ∀ x : ι, Real.log ‖y x‖ ≤ ∑ i, rho i} := by
  intro y hy
  rw [Set.mem_setOf_eq]
  rcases hy with ⟨z, rfl⟩
  intro x
  change Real.log ‖((z x : ℚ_[p]))‖ ≤ ∑ i, rho i
  have hnorm : ‖((z x : ℚ_[p]))‖ ≤ 1 := (z x).2
  have hlog : Real.log ‖((z x : ℚ_[p]))‖ ≤ 0 :=
    Real.log_nonpos (norm_nonneg _) hnorm
  exact hlog.trans (Finset.sum_nonneg (fun i _ => hρ i))

#check coordinateLattice_subset_regionAll
end LeanFormal.IUT.XiFPaper.S2796CoordinateLatticeSubsetAllRegionActual
end
