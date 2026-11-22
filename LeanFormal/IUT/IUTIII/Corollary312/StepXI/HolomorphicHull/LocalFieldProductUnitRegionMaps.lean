import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Continuous product-field maps preserve the holomorphic unit region

All powers of an integral element remain in the compact unit region.
Their images therefore have bounded coordinate norms. In a field a
coordinate with norm greater than one would have unbounded powers.
No norm-isometry or field-factor permutation is assumed for the map.
-/

namespace LeanFormal.IUT.LocalFieldProductHull

open Filter
open scoped Topology

theorem norm_le_one_of_compact_powers {K : Type*} [NormedField K]
    {C : Set K} (hC : IsCompact C) (x : K) (hx : ∀ n : ℕ, x ^ n ∈ C) :
    ‖x‖ ≤ 1 := by
  obtain ⟨y, _, hmax⟩ := hC.exists_isMaxOn ⟨x ^ 0, hx 0⟩ continuous_norm.continuousOn
  have hbound : ∀ n : ℕ, ‖x‖ ^ n ≤ ‖y‖ := by
    intro n
    rw [← norm_pow]
    exact hmax (hx n)
  by_contra hle
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (lt_of_not_ge hle)).eventually
    (eventually_gt_atTop ‖y‖)).exists
  exact not_le_of_gt hn (hbound n)

variable {J L : Type*} {E : J → Type*} {F : L → Type*}
variable [∀ j, NormedField (E j)] [∀ l, NormedField (F l)]

theorem continuous_ringHom_mem_unitRegion [Finite J] [∀ j, ProperSpace (E j)]
    (f : ((j : J) → E j) →+* ((l : L) → F l)) (hf : Continuous f)
    {x : (j : J) → E j} (hx : x ∈ unitRegion (K := E)) :
    f x ∈ unitRegion (K := F) := by
  intro l
  let C := (fun y : (l : L) → F l => y l) '' (f '' unitRegion (K := E))
  have hC : IsCompact C :=
    ((isCompact_unitRegion (K := E)).image hf).image (continuous_apply l)
  apply norm_le_one_of_compact_powers hC
  intro n
  refine ⟨f (x ^ n), ⟨x ^ n, ?_, rfl⟩, ?_⟩
  · intro j
    change ‖(x j) ^ n‖ ≤ 1
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hx j)
  · rw [map_pow]
    rfl

theorem continuous_ringEquiv_mem_unitRegion_iff
    [Finite J] [Finite L] [∀ j, ProperSpace (E j)] [∀ l, ProperSpace (F l)]
    (e : ((j : J) → E j) ≃+* ((l : L) → F l))
    (he : Continuous e) (hinverse : Continuous e.symm) (x : (j : J) → E j) :
    e x ∈ unitRegion (K := F) ↔ x ∈ unitRegion (K := E) := by
  constructor
  · intro hx
    have h := continuous_ringHom_mem_unitRegion e.symm.toRingHom hinverse hx
    change e.symm (e x) ∈ unitRegion (K := E) at h
    simpa only [RingEquiv.symm_apply_apply] using h
  · exact continuous_ringHom_mem_unitRegion e.toRingHom he

theorem continuous_ringEquiv_image_unitRegion
    [Finite J] [Finite L] [∀ j, ProperSpace (E j)] [∀ l, ProperSpace (F l)]
    (e : ((j : J) → E j) ≃+* ((l : L) → F l))
    (he : Continuous e) (hinverse : Continuous e.symm) :
    e '' unitRegion (K := E) = unitRegion (K := F) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (continuous_ringEquiv_mem_unitRegion_iff e he hinverse x).mpr hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact (continuous_ringEquiv_mem_unitRegion_iff e he hinverse (e.symm y)).mp
      (by simpa only [RingEquiv.apply_symm_apply] using hy)

end LeanFormal.IUT.LocalFieldProductHull
