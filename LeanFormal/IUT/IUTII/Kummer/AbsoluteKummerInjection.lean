/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.KummerGaloisClass
import LeanFormal.IUT.IUTII.Kummer.AlgebraicClosureKummerRoots

/-!
  The absolute-Galois Kummer injection `Kˣ / (Kˣ)^n ↪ Hom(G_K, μ_n)`.

  For a field `K` of characteristic zero and `n ≥ 1`, every unit of `K` has an
  `n`-th root in an algebraic closure (imported from
  `AlgebraicClosureKummerRoots`).  When the Galois action on `n`-th roots of
  unity is trivial — in particular when all `n`-th roots of unity of the
  algebraic closure already lie in `K` — the root ratios `σ α / α` define a
  group homomorphism

    `absoluteKummerMap : Kˣ →* Hom(Gal(K̄/K), μ_n(K̄))`.

  Its kernel is proved to be exactly the subgroup of `n`-th powers in `Kˣ`.
  Since the coefficient module has trivial action, continuous `H¹(G_K, μ_n)`
  is the group of continuous homomorphisms `G_K → μ_n`; this map is therefore
  the classical Kummer injection `Kˣ/(Kˣ)^n ↪ H¹(G_K, μ_n)`.

  The fixed-field input for the algebraic closure is
  `fixed_by_absoluteGalois_mem_base`; the root-ratio algebra is
  `KummerGaloisClass`.  No Frobenioid, Θ-link, or arithmetic source object is
  used, and no Kummer isomorphism onto a subgroup of `H¹` is asserted.
-/

namespace LeanFormal.IUT

namespace AbsoluteKummerInjection

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} [NeZero n]

/-- The triviality hypothesis on the Galois action on `n`-th roots of unity in
the algebraic closure.  It holds whenever every `n`-th root of unity of the
algebraic closure lies in `K`; see `rootsOfUnity_fixed_of_mem_base`. -/
def RootsOfUnityFixed : Prop :=
  ∀ ζ : rootsOfUnity n (AlgebraicClosure K),
    ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      σ (((ζ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) =
        ((ζ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)

/-- If all `n`-th roots of unity of the algebraic closure lie in `K`, the
Galois action on them is trivial. -/
theorem rootsOfUnity_fixed_of_mem_base
    (hbase : ∀ ζ : rootsOfUnity n (AlgebraicClosure K),
      ((ζ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ∈
        Set.range (algebraMap K (AlgebraicClosure K))) :
    RootsOfUnityFixed (K := K) (n := n) := by
  intro ζ σ
  obtain ⟨k, hk⟩ := hbase ζ
  calc
    σ (((ζ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) =
        σ (algebraMap K (AlgebraicClosure K) k) := by rw [hk]
    _ = algebraMap K (AlgebraicClosure K) k := σ.commutes k
    _ = ((ζ : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := hk

/-- A chosen `n`-th root of a unit in the algebraic closure. -/
noncomputable def chosenRoot (a : Kˣ) : (AlgebraicClosure K)ˣ :=
  Classical.choose (exists_root_algebraicClosure (K := K) n a)

/-- The chosen root really is an `n`-th root of the image of `a`. -/
theorem chosenRoot_spec (a : Kˣ) :
    chosenRoot (K := K) (n := n) a ^ n =
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a :=
  Classical.choose_spec (exists_root_algebraicClosure (K := K) n a)

/-- The absolute Kummer map `Kˣ →* Hom(Gal(K̄/K), μ_n(K̄))`. -/
noncomputable def absoluteKummerMap
    (hμ : RootsOfUnityFixed (K := K) (n := n)) :
    Kˣ →* ((AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
      rootsOfUnity n (AlgebraicClosure K)) where
  toFun a :=
    KummerGaloisClass.kummerRatioHom hμ
      (chosenRoot (K := K) (n := n) a)
      (chosenRoot_spec (K := K) (n := n) a)
  map_one' := by
    have hone : (1 : (AlgebraicClosure K)ˣ) ^ n =
        Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (1 : Kˣ) := by
      simp
    have hEq :=
      KummerGaloisClass.kummerRatioHom_eq_of_pow_eq hμ
        (chosenRoot_spec (K := K) (n := n) (1 : Kˣ)) hone
    rw [hEq]
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    rw [KummerGaloisClass.kummerRatioHom_apply,
      KummerGaloisClass.kummerRatio_coe_units]
    simp
  map_mul' a b := by
    have hα := chosenRoot_spec (K := K) (n := n) a
    have hβ := chosenRoot_spec (K := K) (n := n) b
    have hαβ :
        (chosenRoot (K := K) (n := n) a *
            chosenRoot (K := K) (n := n) b) ^ n =
          Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (a * b) := by
      rw [mul_pow, hα, hβ, map_mul]
    have hstep1 :=
      KummerGaloisClass.kummerRatioHom_eq_of_pow_eq hμ
        (chosenRoot_spec (K := K) (n := n) (a * b)) hαβ
    have hstep2 :=
      KummerGaloisClass.kummerRatioHom_mul_roots hμ hα hβ hαβ
    exact hstep1.trans hstep2

/-- The absolute Kummer map is computed by the Kummer ratio of the chosen
root. -/
@[simp] theorem absoluteKummerMap_apply
    (hμ : RootsOfUnityFixed (K := K) (n := n)) (a : Kˣ) :
    absoluteKummerMap hμ a =
      KummerGaloisClass.kummerRatioHom hμ
        (chosenRoot (K := K) (n := n) a)
        (chosenRoot_spec (K := K) (n := n) a) := rfl

/-- The kernel of the absolute Kummer map is exactly the subgroup of `n`-th
powers in `Kˣ`.  This is the classical Kummer injection
`Kˣ/(Kˣ)^n ↪ H¹(G_K, μ_n)` for trivial coefficient action. -/
theorem absoluteKummerMap_eq_one_iff
    (hμ : RootsOfUnityFixed (K := K) (n := n)) (a : Kˣ) :
    absoluteKummerMap hμ a = 1 ↔ ∃ b : Kˣ, b ^ n = a := by
  constructor
  · intro h
    have hα := chosenRoot_spec (K := K) (n := n) a
    have hhom : KummerGaloisClass.kummerRatioHom hμ
        (chosenRoot (K := K) (n := n) a) hα = 1 := by
      rw [← absoluteKummerMap_apply]
      exact h
    have hfixed : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
        σ ((chosenRoot (K := K) (n := n) a :
            (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
          ((chosenRoot (K := K) (n := n) a :
            (AlgebraicClosure K)ˣ) : AlgebraicClosure K) :=
      (KummerGaloisClass.kummerRatioHom_eq_one_iff hμ
        (chosenRoot (K := K) (n := n) a) hα).mp
        (fun σ => by rw [hhom]; rfl)
    obtain ⟨b, hb⟩ :=
      fixed_by_absoluteGalois_mem_base
        ((chosenRoot (K := K) (n := n) a :
          (AlgebraicClosure K)ˣ) : AlgebraicClosure K) hfixed
    have hbne : b ≠ 0 := by
      intro hb0
      have hrootZero :
          ((chosenRoot (K := K) (n := n) a :
            (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 0 := by
        rw [← hb, hb0, map_zero]
      exact (chosenRoot (K := K) (n := n) a).ne_zero hrootZero
    refine ⟨Units.mk0 b hbne, ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    apply FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)
    rw [map_pow, hb]
    have hcoe :
        (((chosenRoot (K := K) (n := n) a :
            (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ^ n =
          algebraMap K (AlgebraicClosure K) (a : K) := by
      have := congrArg (fun u : (AlgebraicClosure K)ˣ =>
        (u : AlgebraicClosure K)) hα
      simpa using this
    exact hcoe
  · rintro ⟨b, hb⟩
    have hmapb :
        (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom b) ^ n =
          Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a := by
      rw [← map_pow, hb]
    rw [absoluteKummerMap_apply,
      KummerGaloisClass.kummerRatioHom_eq_of_pow_eq hμ
        (chosenRoot_spec (K := K) (n := n) a) hmapb]
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    rw [KummerGaloisClass.kummerRatioHom_apply,
      KummerGaloisClass.kummerRatio_coe_units]
    have hfix :
        Units.map (σ : AlgebraicClosure K →* AlgebraicClosure K)
            (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom b) =
          Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom b := by
      ext
      simp [AlgEquiv.commutes]
    rw [hfix, div_self']
    rfl

end AbsoluteKummerInjection

end LeanFormal.IUT
