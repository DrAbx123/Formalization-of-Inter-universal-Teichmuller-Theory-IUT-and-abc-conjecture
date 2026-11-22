import tmp.sheaf.xif.paper.S2726PerPlaceUpdateRegionActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2743PerPlaceRegionClosedActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]
variable [∀ i, NeZero (Module.finrank ℚ_[p] (M i))]
variable [DecidableEq ι]

theorem isClosed_log_norm_le_of_nonneg
    (j : FinitePadicTensorIndex (p := p) M) (r : ℝ) (hr : 0 ≤ r) :
    IsClosed {y : FinitePadicTensorIndex (p := p) M → ℚ_[p] |
      Real.log ‖y j‖ ≤ r} := by
  have hset : {y : FinitePadicTensorIndex (p := p) M → ℚ_[p] |
      Real.log ‖y j‖ ≤ r} =
      {y | ‖y j‖ ≤ Real.exp r} := by
    ext y
    simp only [Set.mem_setOf_eq]
    by_cases h : ‖y j‖ = 0
    · have hlog : Real.log ‖y j‖ = 0 := by rw [h, Real.log_zero]
      have hexp : 0 ≤ Real.exp r := le_of_lt (Real.exp_pos r)
      simp [hlog, h, hr, hexp]
    · have hpos : 0 < ‖y j‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
      rw [Real.log_le_iff_le_exp hpos]
  rw [hset]
  exact isClosed_le (continuous_norm.comp (continuous_apply j)) continuous_const

theorem isClosed_perPlaceUpdateRegion
    (rho : ι → ℝ) (hρ : ∀ i, 0 ≤ rho i) :
    IsClosed (S2726PerPlaceUpdateRegion (p := p) M rho) := by
  have hcoord : IsClosed
      {y : FinitePadicTensorIndex (p := p) M → ℚ_[p] |
        ∀ (i : ι) (k : Fin (Module.finrank ℚ_[p] (M i))),
          Real.log ‖y (Function.update (defaultTensorIndex (p := p) M) i k)‖
            ≤ rho i} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter (fun i => by
      rw [Set.setOf_forall]
      exact isClosed_iInter (fun k =>
        isClosed_log_norm_le_of_nonneg (p := p) (M := M)
          (Function.update (defaultTensorIndex (p := p) M) i k)
          (rho i) (hρ i)))
  rw [S2726PerPlaceUpdateRegion]
  have hiso : Isometry (finitePadicTensorCoordinates (p := p) M) := by
    intro x y
    rfl
  exact hcoord.preimage hiso.continuous

#check isClosed_log_norm_le_of_nonneg
#check isClosed_perPlaceUpdateRegion
end LeanFormal.IUT.XiFPaper.S2743PerPlaceRegionClosedActual
end
