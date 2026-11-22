import LeanFormal.IUT.Foundations.PAdicAnalytic.TateContractionGeneral

open Set Metric
open scoped NNReal
open LeanFormal.IUT.PAdicAnalytic.TateContractionGeneral

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.PAdicAnalytic.GeneralInverseJAssembly

noncomputable section

universe u

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem norm_le_of_dist_le_sq (c : ℝ≥0) (hc : c < 1) (t q : K)
    (ht : ‖t‖ ≤ (c : ℝ)) (hq : dist q t ≤ (c : ℝ) ^ 2) : ‖q‖ ≤ (c : ℝ) := by
  have hc2le : (c : ℝ) ^ 2 ≤ (c : ℝ) := by
    nlinarith [c.coe_nonneg, hc]
  calc
    ‖q‖ = dist q 0 := by rw [dist_eq_norm]; simp
    _ ≤ max (dist q t) (dist t 0) := dist_triangle_max q t 0
    _ ≤ max ((c : ℝ) ^ 2) (c : ℝ) :=
      max_le_max hq (by simpa [dist_eq_norm] using ht)
    _ = (c : ℝ) := max_eq_right hc2le

theorem exists_inverseJ_of_remainder
    (H R : K → K) (c : ℝ≥0) (hc : c < 1)
    (hH : ∀ q : K, H q = q + R q)
    (hR_bound : ∀ q : K, ‖q‖ ≤ (c : ℝ) → ‖R q‖ ≤ (c : ℝ) ^ 2)
    (hR_lip : ∀ x y : K, ‖x‖ ≤ (c : ℝ) → ‖y‖ ≤ (c : ℝ) →
      dist (R x) (R y) ≤ (c : ℝ) * dist x y)
    (t : K) (ht : ‖t‖ ≤ (c : ℝ)) :
    ∃ q : K, ‖q‖ ≤ (c : ℝ) ∧ H q = t := by
  have hRmaps : ∀ q : K, dist q t ≤ (c : ℝ) ^ 2 → ‖R q‖ ≤ (c : ℝ) ^ 2 := by
    intro q hq
    exact hR_bound q (norm_le_of_dist_le_sq (c := c) hc t q ht hq)
  have hRcontract : ∀ x y : K, dist x t ≤ (c : ℝ) ^ 2 → dist y t ≤ (c : ℝ) ^ 2 →
      dist (R x) (R y) ≤ (c : ℝ) * dist x y := by
    intro x y hx hy
    exact hR_lip x y
      (norm_le_of_dist_le_sq (c := c) hc t x ht hx)
      (norm_le_of_dist_le_sq (c := c) hc t y ht hy)
  obtain ⟨q, hqle, hq⟩ := exists_tateHGeneral_eq R c t hc ht hRmaps hRcontract
  refine ⟨q, hqle, ?_⟩
  rw [hH q]
  exact hq

end
end LeanFormal.IUT.PAdicAnalytic.GeneralInverseJAssembly