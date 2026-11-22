import LeanFormal.IUT.Foundations.Analysis.BanachFixedPointClosedBall
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

open Set Metric
open scoped NNReal

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.PAdicAnalytic.TateContractionGeneral

noncomputable section

universe u

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (R : K → K) (c : ℝ≥0) (hc : c < 1)

noncomputable def tateHGeneral (q : K) : K := q + R q

noncomputable def tateMapGeneral (t : K) (q : K) : K := t - R q

theorem tateMapGeneral_mapsTo_closedBall
    (t : K)
    (hRmaps : ∀ q : K, dist q t ≤ (c : ℝ) ^ 2 → ‖R q‖ ≤ (c : ℝ) ^ 2) :
    MapsTo (tateMapGeneral R t) (closedBall t ((c : ℝ) ^ 2))
      (closedBall t ((c : ℝ) ^ 2)) := by
  intro q hq
  rw [Metric.mem_closedBall] at hq ⊢
  have hR := hRmaps q hq
  calc
    dist (tateMapGeneral R t q) t = ‖R q‖ := by
      have hsub : tateMapGeneral R t q - t = - R q := by
        unfold tateMapGeneral
        ring
      rw [dist_eq_norm, hsub, norm_neg]
    _ ≤ (c : ℝ) ^ 2 := hR

theorem tateMapGeneral_contracting_on_ball
    (t : K)
    (hRcontract : ∀ x y : K, dist x t ≤ (c : ℝ) ^ 2 → dist y t ≤ (c : ℝ) ^ 2 →
      dist (R x) (R y) ≤ (c : ℝ) * dist x y) :
    ∀ x : K, dist x t ≤ (c : ℝ) ^ 2 → ∀ y : K, dist y t ≤ (c : ℝ) ^ 2 →
      dist (tateMapGeneral R t x) (tateMapGeneral R t y) ≤ (c : ℝ) * dist x y := by
  intro x hx y hy
  calc
    dist (tateMapGeneral R t x) (tateMapGeneral R t y) = dist (R x) (R y) := by
      have hsub : tateMapGeneral R t x - tateMapGeneral R t y = -(R x - R y) := by
        unfold tateMapGeneral
        ring
      rw [dist_eq_norm, dist_eq_norm, hsub, norm_neg]
    _ ≤ (c : ℝ) * dist x y := hRcontract x y hx hy

noncomputable def tateMapGeneralOnBall
    (t : K)
    (hRmaps : ∀ q : K, dist q t ≤ (c : ℝ) ^ 2 → ‖R q‖ ≤ (c : ℝ) ^ 2) :
    closedBall t ((c : ℝ) ^ 2) → closedBall t ((c : ℝ) ^ 2) :=
  fun q => ⟨tateMapGeneral R t q.1,
    tateMapGeneral_mapsTo_closedBall R c t hRmaps q.2⟩

theorem tateMapGeneralOnBall_lipschitz
    (t : K)
    (hRmaps : ∀ q : K, dist q t ≤ (c : ℝ) ^ 2 → ‖R q‖ ≤ (c : ℝ) ^ 2)
    (hRcontract : ∀ x y : K, dist x t ≤ (c : ℝ) ^ 2 → dist y t ≤ (c : ℝ) ^ 2 →
      dist (R x) (R y) ≤ (c : ℝ) * dist x y) :
    LipschitzWith c (tateMapGeneralOnBall R c t hRmaps) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (tateMapGeneral R t x.1) (tateMapGeneral R t y.1) ≤ (c : ℝ) * dist x.1 y.1
  exact tateMapGeneral_contracting_on_ball R c t hRcontract x.1 x.2 y.1 y.2

theorem tateMapGeneralOnBall_contracting
    (t : K) (hc : c < 1)
    (hRmaps : ∀ q : K, dist q t ≤ (c : ℝ) ^ 2 → ‖R q‖ ≤ (c : ℝ) ^ 2)
    (hRcontract : ∀ x y : K, dist x t ≤ (c : ℝ) ^ 2 → dist y t ≤ (c : ℝ) ^ 2 →
      dist (R x) (R y) ≤ (c : ℝ) * dist x y) :
    ContractingWith c (tateMapGeneralOnBall R c t hRmaps) :=
  ⟨hc, tateMapGeneralOnBall_lipschitz R c t hRmaps hRcontract⟩

theorem exists_tateHGeneral_eq
    (t : K) (hc : c < 1) (ht : ‖t‖ ≤ (c : ℝ))
    (hRmaps : ∀ q : K, dist q t ≤ (c : ℝ) ^ 2 → ‖R q‖ ≤ (c : ℝ) ^ 2)
    (hRcontract : ∀ x y : K, dist x t ≤ (c : ℝ) ^ 2 → dist y t ≤ (c : ℝ) ^ 2 →
      dist (R x) (R y) ≤ (c : ℝ) * dist x y) :
    ∃ q : K, ‖q‖ ≤ (c : ℝ) ∧ tateHGeneral R q = t := by
  haveI : IsClosed (closedBall t ((c : ℝ) ^ 2)) := Metric.isClosed_closedBall
  haveI : CompleteSpace (closedBall t ((c : ℝ) ^ 2)) := inferInstance
  have hcont := tateMapGeneralOnBall_contracting R c t hc hRmaps hRcontract
  obtain ⟨z, hz⟩ := hcont.exists_fixedPoint
    (x := ⟨t, by simp [Metric.mem_closedBall]⟩) (by simp)
  have hzt : dist z.1 t ≤ (c : ℝ) ^ 2 := by
    simpa only [Metric.mem_closedBall] using z.2
  have hc2le : (c : ℝ) ^ 2 ≤ (c : ℝ) := by
    nlinarith [c.coe_nonneg, hc]
  have hnorm : ‖z.1‖ ≤ (c : ℝ) := by
    calc
      ‖z.1‖ = dist z.1 0 := by rw [dist_eq_norm]; simp
      _ ≤ max (dist z.1 t) (dist t 0) := dist_triangle_max z.1 t 0
      _ ≤ max ((c : ℝ) ^ 2) (c : ℝ) :=
        max_le_max hzt (by simpa [dist_eq_norm] using ht)
      _ = (c : ℝ) := max_eq_right hc2le
  refine ⟨z.1, hnorm, ?_⟩
  have hv := congrArg Subtype.val hz.1
  change t - R z.1 = z.1 at hv
  unfold tateHGeneral
  linear_combination -hv

end
end LeanFormal.IUT.PAdicAnalytic.TateContractionGeneral