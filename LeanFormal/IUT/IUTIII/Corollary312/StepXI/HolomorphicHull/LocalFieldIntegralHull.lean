import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# The nonarchimedean hull as an actual module over the integral ring

The `O` in the `lambda * O` construction of IUT III Remark 3.9.5(i) is
an integral ring, not the full field or a multiplicative scaling monoid.
This module proves the ring and module closure laws of the analytic regions
constructed in `LocalFieldProductHull`. Only the nonarchimedean norm law is
assumed here; all the integral ring/module structure is constructed from it.

This is the local-field analytic prerequisite of N4--N7, not a reconstruction
of the source log-shell from an abstract prime strip.
-/

namespace LeanFormal.IUT.LocalFieldProductHull

variable {ι : Type*} {K : ι → Type*} [∀ i, NormedField (K i)]

/-- The product of the nonarchimedean rings of integers, constructed directly
as a subring of the ambient field product. -/
def integralRing (hna : ∀ i, IsNonarchimedean (Norm.norm : K i → ℝ)) :
    Subring ((i : ι) → K i) where
  carrier := unitRegion
  zero_mem' := by intro i; simp
  one_mem' := by intro i; simp
  add_mem' := by
    intro x y hx hy i
    exact (hna i (x i) (y i)).trans (max_le (hx i) (hy i))
  neg_mem' := by
    intro x hx i
    simpa only [Pi.neg_apply, norm_neg] using hx i
  mul_mem' := by
    intro x y hx hy i
    change ‖x i * y i‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hx i)).trans (hy i)

/-- Each coordinate disc product is an actual `O`-submodule. In particular,
it is stable under integral scalars, rather than all nonzero field scalars. -/
def regionModule (hna : ∀ i, IsNonarchimedean (Norm.norm : K i → ℝ))
    (lam : (i : ι) → K i) : Submodule (integralRing hna) ((i : ι) → K i) where
  carrier := region lam
  zero_mem' := by
    intro i
    simpa only [Pi.zero_apply, norm_zero] using norm_nonneg (lam i)
  add_mem' := by
    intro x y hx hy i
    exact (hna i (x i) (y i)).trans (max_le (hx i) (hy i))
  smul_mem' := by
    intro r x hx i
    change ‖(r : (i : ι) → K i) i * x i‖ ≤ ‖lam i‖
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (r.property i)).trans (hx i)

theorem integralRing_carrier (hna : ∀ i, IsNonarchimedean (Norm.norm : K i → ℝ)) :
    (integralRing hna : Set ((i : ι) → K i)) = unitRegion := rfl

theorem regionModule_carrier (hna : ∀ i, IsNonarchimedean (Norm.norm : K i → ℝ))
    (lam : (i : ι) → K i) :
    (regionModule hna lam : Set ((i : ι) → K i)) = region lam := rfl

/-- Every nondegenerate relatively compact input has a compact integral-module
hull, with the precise nonzero coordinate hypotheses of the hull construction. -/
theorem exists_compact_integralModule_hull [Finite ι] [∀ i, ProperSpace (K i)]
    (hna : ∀ i, IsNonarchimedean (Norm.norm : K i → ℝ))
    {S : Set ((i : ι) → K i)} (hS : IsCompact (closure S)) (hne : S.Nonempty)
    (hcoord : ∀ i, ∃ x ∈ S, x i ≠ 0) :
    ∃ H : Submodule (integralRing hna) ((i : ι) → K i),
      (H : Set ((i : ι) → K i)) = hull S ∧ IsCompact (H : Set ((i : ι) → K i)) := by
  obtain ⟨lam, _, heq⟩ := exists_hull_eq_region_of_isCompact_closure hS hne hcoord
  exact ⟨regionModule hna lam, heq.symm, isCompact_region lam⟩

end LeanFormal.IUT.LocalFieldProductHull
