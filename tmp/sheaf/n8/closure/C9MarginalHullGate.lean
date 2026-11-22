import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Marginal support criterion for the holomorphic-hull gate

The carrier containment tested here is coordinatewise.  Its maximizing
coordinates may come from different points of the output family; no global
assembly of those points is needed for the geometric hull or for a weighted
log-radius bound with a common reference.

This file proves only the geometric and ordered-log implications.  Identifying
the q-pilot coordinates and the output projections for a paper-admissible C
remains a separate source obligation.
-/

open Metric
open LeanFormal.IUT.LocalFieldProductHull

namespace LeanFormal.IUT.MarginalHullGate

variable {ι : Type*} {K : ι → Type*} [∀ i, NormedField (K i)]

/-- Containment of one product carrier in another is exactly coordinatewise
radius domination. -/
theorem region_subset_region_iff (q lam : (i : ι) → K i) :
    region q ⊆ region lam ↔ ∀ i, ‖q i‖ ≤ ‖lam i‖ := by
  constructor
  · intro h i
    have hq : q ∈ region q := by
      intro j
      exact le_rfl
    exact h hq i
  · intro h x hx i
    exact le_trans (hx i) (h i)

/-- A compact, coordinatewise nondegenerate output carrier contains the q
carrier exactly when one (hence its canonical least) hull radius dominates
each q-coordinate.  The maximizing point may depend on the coordinate. -/
theorem exists_marginal_hull_certificate_iff
    [Finite ι] [∀ i, ProperSpace (K i)]
    {S : Set ((i : ι) → K i)} (q : (i : ι) → K i)
    (hS : IsCompact (closure S)) (hne : S.Nonempty)
    (hcoord : ∀ i, ∃ x ∈ S, x i ≠ 0) :
    region q ⊆ hull S ↔
      ∃ lam : (i : ι) → K i,
        (∀ i, lam i ≠ 0) ∧ hull S = region lam ∧
        (∀ i, ‖q i‖ ≤ ‖lam i‖) := by
  constructor
  · intro hq
    obtain ⟨lam, hlam, hhull⟩ :=
      exists_hull_eq_region_of_isCompact_closure hS hne hcoord
    have hbound : ∀ i, ‖q i‖ ≤ ‖lam i‖ := by
      intro i
      have hq' : region q ⊆ region lam := by
        simpa only [hhull] using hq
      exact (region_subset_region_iff q lam).mp hq' i
    exact ⟨lam, hlam, hhull, hbound⟩
  · rintro ⟨lam, hlam, hhull, hbound⟩
    rw [hhull]
    exact (region_subset_region_iff q lam).mpr hbound

/-- Pointwise support formulation: containment in the hull is equivalent to
each q-coordinate radius being bounded by some point of the compact closure.
The point witnessing the bound is allowed to depend on the coordinate. -/
theorem hull_contains_region_iff_marginal_support
    [Finite ι] [∀ i, ProperSpace (K i)]
    {S : Set ((i : ι) → K i)} (q : (i : ι) → K i)
    (hS : IsCompact (closure S)) (hne : S.Nonempty)
    (hcoord : ∀ i, ∃ x ∈ S, x i ≠ 0) :
    region q ⊆ hull S ↔
      ∀ i, ∃ x ∈ closure S, ‖q i‖ ≤ ‖x i‖ := by
  have hneC : (closure S).Nonempty := hne.mono subset_closure
  have hcoordC : ∀ i, ∃ x ∈ closure S, x i ≠ 0 := by
    intro i
    obtain ⟨x, hxS, hxi⟩ := hcoord i
    exact ⟨x, subset_closure hxS, hxi⟩
  obtain ⟨lam, hrealized, hbound⟩ :=
    exists_coordinate_maxima (S := closure S) hS hneC
  have hlam0 : ∀ i, lam i ≠ 0 := by
    intro i
    obtain ⟨x, hx, hxi⟩ := hcoordC i
    have hxle : ‖x i‖ ≤ ‖lam i‖ := hbound hx i
    exact norm_pos_iff.mp (lt_of_lt_of_le (norm_pos_iff.mpr hxi) hxle)
  have hhull : hull S = region lam := by
    rw [← hull_closure (S := S)]
    apply Set.Subset.antisymm
    · exact hull_minimal hlam0 (hbound)
    · intro x hx mu hmu hC i
      obtain ⟨w, hwC, hw⟩ := hrealized i
      exact le_trans (hx i) (by rw [hw]; exact hC hwC i)
  constructor
  · intro hq i
    have hqi : q ∈ hull S := hq (by intro j; exact le_rfl)
    rw [hhull] at hqi
    obtain ⟨x, hxC, hxi⟩ := hrealized i
    refine ⟨x, hxC, ?_⟩
    exact le_trans (hqi i) (by rw [hxi])
  · intro hq
    rw [hhull]
    apply (region_subset_region_iff q lam).mpr
    intro i
    obtain ⟨x, hxC, hqx⟩ := hq i
    exact le_trans hqx (hbound hxC i)

/-- Weighted log radii are monotone under coordinatewise carrier inclusion.
The offset is the same reference correction on both sides, and M is the same
nonnegative tensor-power factor. -/
theorem weighted_logReadout_mono
    [Fintype ι] (w refLog : ι → ℝ) (M : ℝ)
    (q lam : (i : ι) → K i)
    (hw : ∀ i, 0 ≤ w i) (hM : 0 ≤ M)
    (hq0 : ∀ i, q i ≠ 0)
    (hbound : ∀ i, ‖q i‖ ≤ ‖lam i‖) :
    (∑ i, w i * (M * Real.log ‖q i‖ + refLog i)) ≤
      ∑ i, w i * (M * Real.log ‖lam i‖ + refLog i) := by
  apply Finset.sum_le_sum
  intro i hi
  have hlog : Real.log ‖q i‖ ≤ Real.log ‖lam i‖ :=
    Real.log_le_log (norm_pos_iff.mpr (hq0 i)) (hbound i)
  have hscaled : M * Real.log ‖q i‖ ≤ M * Real.log ‖lam i‖ :=
    mul_le_mul_of_nonneg_left hlog hM
  have hterm :
      M * Real.log ‖q i‖ + refLog i ≤
        M * Real.log ‖lam i‖ + refLog i :=
    add_le_add hscaled le_rfl
  exact mul_le_mul_of_nonneg_left hterm (hw i)

end LeanFormal.IUT.MarginalHullGate
