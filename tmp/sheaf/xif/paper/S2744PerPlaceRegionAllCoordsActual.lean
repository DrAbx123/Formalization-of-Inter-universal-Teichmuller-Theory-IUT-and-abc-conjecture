import tmp.sheaf.xif.paper.S2743PerPlaceRegionClosedActual
import tmp.sheaf.xif.paper.S2726PerPlaceUpdateRegionActual
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

noncomputable section
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2744PerPlaceRegionAllCoordsActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2743PerPlaceRegionClosedActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]
variable [∀ i, NeZero (Module.finrank ℚ_[p] (M i))]
variable [DecidableEq ι]

local instance s2744Meas : MeasurableSpace (FinitePadicTensor (p := p) M) := borel _
local instance s2744Borel : BorelSpace (FinitePadicTensor (p := p) M) := ⟨rfl⟩

/-- Corrected per-place region: every tensor coordinate is bounded by the sum of the per-place log bounds. -/
noncomputable def S2726PerPlaceUpdateRegionAll
    (rho : ι → ℝ) : Set (FinitePadicTensor (p := p) M) :=
  (finitePadicTensorCoordinates (p := p) M) ⁻¹'
    { y | ∀ x : FinitePadicTensorIndex (p := p) M,
        Real.log ‖y x‖ ≤ ∑ i, rho i }

theorem log_norm_le_iff_norm_le_exp_of_nonneg
    (r : ℝ) (hr : 0 ≤ r) (z : ℚ_[p]) :
    Real.log ‖z‖ ≤ r ↔ ‖z‖ ≤ Real.exp r := by
  by_cases h : ‖z‖ = 0
  · have hlog : Real.log ‖z‖ = 0 := by rw [h, Real.log_zero]
    have hexp : 0 ≤ Real.exp r := le_of_lt (Real.exp_pos r)
    simp [hlog, h, hr, hexp]
  · have hpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    rw [Real.log_le_iff_le_exp hpos]

theorem isClosed_perPlaceUpdateRegionAll
    (rho : ι → ℝ) (hρ : ∀ i, 0 ≤ rho i) :
    IsClosed (S2726PerPlaceUpdateRegionAll (p := p) M rho) := by
  have hR : 0 ≤ ∑ i, rho i := Finset.sum_nonneg (fun i _ => hρ i)
  have hcoord : IsClosed
      {y : FinitePadicTensorIndex (p := p) M → ℚ_[p] |
        ∀ x, Real.log ‖y x‖ ≤ ∑ i, rho i} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter (fun x =>
      isClosed_log_norm_le_of_nonneg (p := p) (M := M) x _ hR)
  rw [S2726PerPlaceUpdateRegionAll]
  have hiso : Isometry (finitePadicTensorCoordinates (p := p) M) := by
    intro x y
    rfl
  exact hcoord.preimage hiso.continuous

theorem isCompact_perPlaceUpdateRegionAll
    (rho : ι → ℝ) (hρ : ∀ i, 0 ≤ rho i) :
    IsCompact (S2726PerPlaceUpdateRegionAll (p := p) M rho) := by
  have hR : 0 ≤ ∑ i, rho i := Finset.sum_nonneg (fun i _ => hρ i)
  have hset : {y : FinitePadicTensorIndex (p := p) M → ℚ_[p] |
      ∀ x, Real.log ‖y x‖ ≤ ∑ i, rho i} =
      Set.univ.pi (fun _ : FinitePadicTensorIndex (p := p) M =>
        Metric.closedBall (0 : ℚ_[p]) (Real.exp (∑ i, rho i))) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Metric.mem_closedBall, dist_zero_right]
    exact forall_congr' (fun x =>
      log_norm_le_iff_norm_le_exp_of_nonneg _ hR (y x))
  have hcompactPi : IsCompact
      (Set.univ.pi (fun _ : FinitePadicTensorIndex (p := p) M =>
        Metric.closedBall (0 : ℚ_[p]) (Real.exp (∑ i, rho i)))) :=
    isCompact_univ_pi (fun _ => ProperSpace.isCompact_closedBall 0 _)
  have hcompactCoord : IsCompact
      {y : FinitePadicTensorIndex (p := p) M → ℚ_[p] |
        ∀ x, Real.log ‖y x‖ ≤ ∑ i, rho i} := by
    rw [hset]
    exact hcompactPi
  rw [S2726PerPlaceUpdateRegionAll]
  have hiso : Isometry (finitePadicTensorCoordinates (p := p) M) := by
    intro x y
    rfl
  let hhomeo := hiso.isEmbedding.toHomeomorphOfSurjective
    (finitePadicTensorCoordinates (p := p) M).surjective
  exact hhomeo.isCompact_preimage.mpr hcompactCoord

theorem measure_lt_top_perPlaceUpdateRegionAll
    (rho : ι → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (μ : Measure (FinitePadicTensor (p := p) M))
    [IsFiniteMeasureOnCompacts μ] :
    μ (S2726PerPlaceUpdateRegionAll (p := p) M rho) < ⊤ :=
  IsCompact.measure_lt_top (isCompact_perPlaceUpdateRegionAll (p := p) M rho hρ)

#check isClosed_perPlaceUpdateRegionAll
#check isCompact_perPlaceUpdateRegionAll

theorem log_le_sum_of_norm_le_one
    (rho : ι → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (y : FinitePadicTensorIndex (p := p) M → ℚ_[p])
    (hy : ∀ j, ‖y j‖ ≤ 1) :
    ∀ j, Real.log ‖y j‖ ≤ ∑ i, rho i := by
  intro j
  exact (Real.log_nonpos (norm_nonneg _) (hy j)).trans
    (Finset.sum_nonneg (fun i _ => hρ i))

#check log_le_sum_of_norm_le_one

#check measure_lt_top_perPlaceUpdateRegionAll
end LeanFormal.IUT.XiFPaper.S2744PerPlaceRegionAllCoordsActual
end
