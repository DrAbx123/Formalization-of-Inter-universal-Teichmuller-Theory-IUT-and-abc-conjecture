import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

noncomputable section
open CategoryTheory Limits

namespace W10SpectralNoGo

abbrev G (n : ℕ) := Multiplicative (ZMod n)

def trivialRep (n : ℕ) : Rep ℝ (G n) := Rep.trivial ℝ (G n) ℝ

def gen (n : ℕ) : G n := Multiplicative.ofAdd (1 : ZMod n)

lemma gen_generates (n : ℕ) [NeZero n] :
    ∀ x : G n, x ∈ Subgroup.zpowers (gen n) := by
  intro x
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := n) (Multiplicative.toAdd x)
  have hy : Multiplicative.toAdd x ∈ AddSubgroup.zmultiples (1 : ZMod n) := by
    rw [← hk]
    simpa only [zsmul_one] using AddSubgroup.intCast_mem_zmultiples_one (R := ZMod n) k
  have hset := ofAdd_image_zmultiples_eq_zpowers_ofAdd (x := (1 : ZMod n))
  have hxmem : x ∈ (Multiplicative.ofAdd '' (AddSubgroup.zmultiples (1 : ZMod n) : Set (ZMod n))) := by
    exact ⟨Multiplicative.toAdd x, hy, rfl⟩
  simpa [gen, hset] using hxmem

lemma normHomCompSub_exact (n : ℕ) [NeZero n] :
    (Rep.FiniteCyclicGroup.normHomCompSub (trivialRep n) (gen n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  let S := Rep.FiniteCyclicGroup.normHomCompSub (trivialRep n) (gen n)
  have hf : S.f.hom = (Fintype.card (G n) : ℝ) • (1 : ℝ →ₗ[ℝ] ℝ) := by
    change (Representation.trivial ℝ (G n) ℝ).norm = _
    ext x
    simp [Representation.norm]
  have hg : S.g.hom = 0 := by
    have happ : (trivialRep n).applyAsHom (gen n) = 𝟙 (trivialRep n) := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    have hsub : (Rep.applyAsHom (trivialRep n) (gen n) - 𝟙 (trivialRep n)) = 0 := by
      rw [happ, sub_self]
    change (Rep.applyAsHom (trivialRep n) (gen n) - 𝟙 (trivialRep n)).hom.toLinearMap = 0
    rw [hsub]
    rfl
  rw [hf, hg]
  have hcard : (Fintype.card (G n) : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card (G n) := Fintype.card_pos_iff.mpr ⟨1⟩
    exact_mod_cast hpos.ne'
  ext x
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨(Fintype.card (G n) : ℝ)⁻¹ * x, ?_⟩
    change (Fintype.card (G n) : ℝ) • ((Fintype.card (G n) : ℝ)⁻¹ * x) = x
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]

lemma subCompNormHom_exact (n : ℕ) [NeZero n] :
    (Rep.FiniteCyclicGroup.subCompNormHom (trivialRep n) (gen n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  let S := Rep.FiniteCyclicGroup.subCompNormHom (trivialRep n) (gen n)
  have hf : S.f.hom = 0 := by
    have happ : (trivialRep n).applyAsHom (gen n) = 𝟙 (trivialRep n) := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    have hsub : (Rep.applyAsHom (trivialRep n) (gen n) - 𝟙 (trivialRep n)) = 0 := by
      rw [happ, sub_self]
    change (Rep.applyAsHom (trivialRep n) (gen n) - 𝟙 (trivialRep n)).hom.toLinearMap = 0
    rw [hsub]
    rfl
  have hg : S.g.hom = (Fintype.card (G n) : ℝ) • (1 : ℝ →ₗ[ℝ] ℝ) := by
    change (Representation.trivial ℝ (G n) ℝ).norm = _
    ext x
    simp [Representation.norm]
  rw [hf, hg, LinearMap.range_zero]
  change (⊥ : Submodule ℝ ℝ) = LinearMap.ker ((Fintype.card (G n) : ℝ) • (1 : ℝ →ₗ[ℝ] ℝ))
  have hcard : (Fintype.card (G n) : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card (G n) := Fintype.card_pos_iff.mpr ⟨1⟩
    exact_mod_cast hpos.ne'
  rw [LinearMap.ker_smul (1 : ℝ →ₗ[ℝ] ℝ) (Fintype.card (G n) : ℝ) hcard]
  change (⊥ : Submodule ℝ ℝ) = LinearMap.ker (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  rw [LinearMap.ker_id]

/-- Positive-degree group cohomology of mu_{2l} with real coefficients vanishes. -/
theorem groupCohomology_trivial_vanishes (n : ℕ) [NeZero n] (i : ℕ) (hi : 0 < i) :
    IsZero (groupCohomology (trivialRep n) i) := by
  rcases Nat.even_or_odd i with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · haveI : NeZero (k + k) := ⟨by omega⟩
    let iso := Rep.FiniteCyclicGroup.groupCohomologyIsoEven (trivialRep n) (gen n)
      (gen_generates n) (k + k) (by simpa [two_mul] using even_two_mul k)
    exact (Iso.isZero_iff iso).mpr
      ((ShortComplex.exact_iff_isZero_homology _).mp (normHomCompSub_exact n))
  · let iso := Rep.FiniteCyclicGroup.groupCohomologyIsoOdd (trivialRep n) (gen n)
      (gen_generates n) (2 * k + 1) (odd_two_mul_add_one k)
    exact (Iso.isZero_iff iso).mpr
      ((ShortComplex.exact_iff_isZero_homology _).mp (subCompNormHom_exact n))

end W10SpectralNoGo
