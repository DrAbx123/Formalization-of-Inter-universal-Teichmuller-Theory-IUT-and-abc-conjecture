import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductUnitRegionMaps

/-!
# The holomorphic hull commutes with topological ring equivalences

Continuous ring equivalences preserve the product unit region. Units
preserve the nonzero-coordinate condition, so they also preserve the
entire family of admissible lambda*O regions. The intersection defining
the hull therefore commutes with the equivalence, for every input set.
-/

namespace LeanFormal.IUT.LocalFieldProductHull

noncomputable section

variable {J L : Type*} {E : J → Type*} {F : L → Type*}
variable [∀ j, NormedField (E j)] [∀ l, NormedField (F l)]

theorem ringEquiv_nonzero_coordinates
    (e : ((j : J) → E j) ≃+* ((l : L) → F l))
    (lam : (j : J) → E j) (hlam : ∀ j, lam j ≠ 0) : ∀ l, e lam l ≠ 0 := by
  have hproduct : e lam * e (fun j => (lam j)⁻¹) = 1 := by
    rw [← map_mul]
    have hinverse : lam * (fun j => (lam j)⁻¹) = 1 := by
      ext j
      exact mul_inv_cancel₀ (hlam j)
    rw [hinverse, map_one]
  intro l hzero
  have hcoordinate := congrArg (fun x : (l : L) → F l => x l) hproduct
  change e lam l * e (fun j => (lam j)⁻¹) l = 1 at hcoordinate
  rw [hzero, zero_mul] at hcoordinate
  exact zero_ne_one hcoordinate

variable [Finite J] [Finite L] [∀ j, ProperSpace (E j)] [∀ l, ProperSpace (F l)]

theorem continuous_ringEquiv_image_region
    (e : ((j : J) → E j) ≃+* ((l : L) → F l))
    (he : Continuous e) (hinverse : Continuous e.symm)
    (lam : (j : J) → E j) (hlam : ∀ j, lam j ≠ 0) :
    e '' region lam = region (e lam) := by
  rw [region_eq_mul_unitRegion lam hlam,
    region_eq_mul_unitRegion (e lam) (ringEquiv_nonzero_coordinates e lam hlam)]
  have hunits := continuous_ringEquiv_image_unitRegion e he hinverse
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨e x, (continuous_ringEquiv_mem_unitRegion_iff e he hinverse x).mpr hx,
      (e.map_mul lam x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← hunits] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨lam * z, ⟨z, hz, rfl⟩, e.map_mul lam z⟩

theorem continuous_ringEquiv_image_hull_subset
    (e : ((j : J) → E j) ≃+* ((l : L) → F l))
    (he : Continuous e) (hinverse : Continuous e.symm) (S : Set ((j : J) → E j)) :
    e '' hull S ⊆ hull (e '' S) := by
  rintro _ ⟨x, hx, rfl⟩ mu hmu hsub
  have hnonzero := ringEquiv_nonzero_coordinates e.symm mu hmu
  have hregion := continuous_ringEquiv_image_region e he hinverse (e.symm mu) hnonzero
  rw [RingEquiv.apply_symm_apply] at hregion
  have hpull : S ⊆ region (e.symm mu) := by
    intro s hs
    have hmember : e s ∈ e '' region (e.symm mu) := by
      rw [hregion]
      exact hsub ⟨s, hs, rfl⟩
    obtain ⟨z, hz, hzs⟩ := hmember
    exact e.injective hzs ▸ hz
  have hpoint : e x ∈ e '' region (e.symm mu) :=
    ⟨x, hx (e.symm mu) hnonzero hpull, rfl⟩
  rwa [hregion] at hpoint

theorem continuous_ringEquiv_image_hull
    (e : ((j : J) → E j) ≃+* ((l : L) → F l))
    (he : Continuous e) (hinverse : Continuous e.symm) (S : Set ((j : J) → E j)) :
    e '' hull S = hull (e '' S) := by
  apply Set.Subset.antisymm (continuous_ringEquiv_image_hull_subset e he hinverse S)
  intro y hy
  have hback := continuous_ringEquiv_image_hull_subset e.symm hinverse he (e '' S)
    ⟨y, hy, rfl⟩
  have hpull : e.symm y ∈ hull S := by
    simp only [Set.image_image, RingEquiv.symm_apply_apply] at hback
    change e.symm y ∈ hull (id '' S) at hback
    rw [Set.image_id] at hback
    exact hback
  exact ⟨e.symm y, hpull, e.apply_symm_apply y⟩

end

end LeanFormal.IUT.LocalFieldProductHull
