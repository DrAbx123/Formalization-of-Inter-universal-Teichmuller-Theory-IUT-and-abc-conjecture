/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
  The classical injectivity statement for finite Galois Kummer theory.

  Let `K ⊆ L` be a finite Galois extension and `n ≥ 1`.  Suppose that the
  Galois action on `L` fixes every `n`-th root of unity in `L`; this holds for
  instance when `μ_n ⊆ K`.  For a unit `α` of `L` with `α ^ n = a` for some
  `a : Kˣ`, the ratios `σ α / α` are `n`-th roots of unity, and they form a
  group homomorphism `Gal(L/K) → μ_n(L)`.

  The main results are:

  * `kummerRatio_pow_eq_one` and `kummerRatioHom`: the ratio is a root of
    unity and is multiplicative in the Galois variable;
  * `kummerRatioHom_eq_of_root_mul`: multiplying a root by an `n`-th root of
    unity does not change the resulting homomorphism;
  * `kummerRatioHom_eq_one_iff`: the homomorphism is trivial exactly when the
    chosen root is fixed by the whole Galois group;
  * `kummer_pow_mem_of_trivial`: a fixed root lies in `K`, so the value `a` is
    an `n`-th power in `Kˣ`;
  * `kummerRootSubgroup` and `kummerMap`: the subgroup of `Kˣ` consisting of
    `n`-th powers from `L`, and the induced map to `Hom(Gal(L/K), μ_n(L))`
    whose kernel is the subgroup of `n`-th powers in `Kˣ`.

  No Frobenioid, `Θ`-link, or arithmetic input is used: this file isolates the
  field-theoretic Kummer injection on which those later layers rely.
-/

namespace LeanFormal.IUT

namespace KummerGaloisClass

-- `n ≥ 1` is part of the frozen interface of the classical Kummer statement.
-- Most field-theoretic identities below remain meaningful for `n = 0`, so the
-- instance is a standing hypothesis rather than a proof ingredient.
set_option linter.unusedSectionVars false

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {n : ℕ} [NeZero n]

/-- The ratio `σ α / α` attached to a unit `α : Lˣ` whose `n`-th power descends
to `K`.  Its underlying value in `L` is `σ α / α`, where `σ` acts on `α` through
its coercion to a monoid homomorphism `L →* L`.

The ratio is an `n`-th root of unity because `σ` fixes the value `a : Kˣ` of
`α ^ n`. -/
def kummerRatio {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (σ : L ≃ₐ[K] L) : rootsOfUnity n L :=
  ⟨Units.map (σ : L →* L) α / α, by
    rw [mem_rootsOfUnity, div_pow, ← map_pow, hα]
    have hfix :
        Units.map (σ : L →* L) (Units.map (algebraMap K L).toMonoidHom a) =
          Units.map (algebraMap K L).toMonoidHom a := by
      ext
      simp [AlgEquiv.commutes]
    rw [hfix, div_self']⟩

/-- The underlying unit of `kummerRatio α hα σ` is `σ α / α`. -/
@[simp] theorem kummerRatio_coe_units {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (σ : L ≃ₐ[K] L) :
    ((kummerRatio α hα σ : rootsOfUnity n L) : Lˣ) =
      Units.map (σ : L →* L) α / α := rfl

/-- The underlying value of `kummerRatio α hα σ` in `L` is `σ α / α`. -/
@[simp] theorem kummerRatio_coe {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (σ : L ≃ₐ[K] L) :
    (((kummerRatio α hα σ : rootsOfUnity n L) : Lˣ) : L) =
      σ (α : L) / (α : L) := by
  simp [kummerRatio_coe_units]

/-- The Kummer ratio is an `n`-th root of unity. -/
theorem kummerRatio_pow_eq_one {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (σ : L ≃ₐ[K] L) :
    kummerRatio α hα σ ^ n = 1 := by
  apply Subtype.ext
  simpa using (kummerRatio α hα σ).2

/-- The Galois action fixes every Kummer ratio, by the hypothesis `hμ` that the
Galois action is trivial on the `n`-th roots of unity. -/
theorem kummerRatio_galois_fixed
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (σ τ : L ≃ₐ[K] L) :
    σ (((kummerRatio α hα τ : rootsOfUnity n L) : Lˣ) : L) =
      (((kummerRatio α hα τ : rootsOfUnity n L) : Lˣ) : L) :=
  hμ (kummerRatio α hα τ) σ

/-- Unit-level form of `kummerRatio_galois_fixed`. -/
theorem kummerRatio_galois_fixed_units
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (σ τ : L ≃ₐ[K] L) :
    Units.map (σ : L →* L) ((kummerRatio α hα τ : rootsOfUnity n L) : Lˣ) =
      ((kummerRatio α hα τ : rootsOfUnity n L) : Lˣ) := by
  apply Units.ext
  exact hμ (kummerRatio α hα τ) σ

/-- The Kummer ratio of the identity is trivial. -/
theorem kummerRatio_one {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a) :
    kummerRatio α hα (1 : L ≃ₐ[K] L) = 1 := by
  apply Subtype.ext
  rw [kummerRatio_coe_units]
  have hone : Units.map ((1 : L ≃ₐ[K] L) : L →* L) α = α := by
    ext
    simp
  rw [hone, div_self']
  rfl

/-- The Kummer ratio is multiplicative in the Galois variable.  This is where
the hypothesis `hμ` enters: `σ` fixes the root-of-unity ratio attached to `τ`. -/
theorem kummerRatio_mul
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (σ τ : L ≃ₐ[K] L) :
    kummerRatio α hα (σ * τ) = kummerRatio α hα σ * kummerRatio α hα τ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, kummerRatio_coe_units, kummerRatio_coe_units,
    kummerRatio_coe_units]
  change Units.map (σ : L →* L) (Units.map (τ : L →* L) α) / α =
    (Units.map (σ : L →* L) α / α) * (Units.map (τ : L →* L) α / α)
  have hfix := kummerRatio_galois_fixed_units hμ α hα σ τ
  rw [kummerRatio_coe_units] at hfix
  have hsplit : Units.map (σ : L →* L) (Units.map (τ : L →* L) α) =
      (Units.map (τ : L →* L) α / α) * Units.map (σ : L →* L) α := by
    conv_lhs => rw [← div_mul_cancel (Units.map (τ : L →* L) α) α]
    rw [map_mul, hfix]
  rw [hsplit, mul_div_assoc]
  exact mul_comm _ _

/-- The Kummer ratio as a monoid homomorphism `Gal(L/K) → μ_n(L)`. -/
def kummerRatioHom
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a) :
    (L ≃ₐ[K] L) →* rootsOfUnity n L where
  toFun := kummerRatio α hα
  map_one' := kummerRatio_one α hα
  map_mul' := kummerRatio_mul hμ α hα

/-- The homomorphism `kummerRatioHom` is computed by `kummerRatio`. -/
@[simp] theorem kummerRatioHom_apply
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (σ : L ≃ₐ[K] L) :
    kummerRatioHom hμ α hα σ = kummerRatio α hα σ := rfl

/-- The multiplicativity statement for `kummerRatioHom`, restated for direct
use. -/
theorem kummerRatioHom_mul
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (σ τ : L ≃ₐ[K] L) :
    kummerRatioHom hμ α hα (σ * τ) =
      kummerRatioHom hμ α hα σ * kummerRatioHom hμ α hα τ :=
  map_mul _ _ _

/-- Multiplying a chosen `n`-th root by an `n`-th root of unity does not change
the Kummer homomorphism. -/
theorem kummerRatioHom_eq_of_root_mul
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a : Kˣ} {α α' : Lˣ}
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (hα' : α' ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (ζ : rootsOfUnity n L) (hζ : α' = (ζ : Lˣ) * α) :
    kummerRatioHom hμ α' hα' = kummerRatioHom hμ α hα := by
  apply MonoidHom.ext
  intro σ
  rw [kummerRatioHom_apply, kummerRatioHom_apply]
  apply Subtype.ext
  rw [kummerRatio_coe_units, kummerRatio_coe_units, hζ, map_mul]
  have hfix : Units.map (σ : L →* L) (ζ : Lˣ) = (ζ : Lˣ) := by
    apply Units.ext
    exact hμ ζ σ
  rw [hfix]
  exact mul_div_mul_left_eq_div (Units.map (σ : L →* L) α) α (ζ : Lˣ)

/-- The Kummer homomorphism is trivial if and only if the chosen root is fixed
by the whole Galois group. -/
theorem kummerRatioHom_eq_one_iff
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a) :
    (∀ σ : L ≃ₐ[K] L, kummerRatioHom hμ α hα σ = 1) ↔
      ∀ σ : L ≃ₐ[K] L, σ (α : L) = (α : L) := by
  constructor
  · intro h σ
    have hσ : kummerRatio α hα σ = 1 := by
      rw [← kummerRatioHom_apply hμ α hα σ]
      rw [h σ]
    have hval : (((kummerRatio α hα σ : rootsOfUnity n L) : Lˣ) : L) = 1 := by
      rw [hσ]
      rfl
    rw [kummerRatio_coe] at hval
    exact (div_eq_one_iff_eq α.ne_zero).mp hval
  · intro h σ
    apply Subtype.ext
    rw [kummerRatioHom_apply, kummerRatio_coe_units]
    have hfix : Units.map (σ : L →* L) α = α := by
      apply Units.ext
      exact h σ
    rw [hfix, div_self']
    rfl

/-- The subgroup of `Kˣ` consisting of elements that acquire an `n`-th root in
`L`. -/
def kummerRootSubgroup : Subgroup Kˣ where
  carrier := {a : Kˣ | ∃ b : Lˣ, b ^ n = Units.map (algebraMap K L).toMonoidHom a}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a a' ⟨b, hb⟩ ⟨b', hb'⟩
    exact ⟨b * b', by rw [mul_pow, hb, hb', map_mul]⟩
  inv_mem' := by
    rintro a ⟨b, hb⟩
    exact ⟨b⁻¹, by rw [inv_pow, hb, map_inv]⟩

/-- Two `n`-th roots of the same element of `Kˣ` define the same Kummer
homomorphism. -/
theorem kummerRatioHom_eq_of_pow_eq
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a : Kˣ} {α β : Lˣ}
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) :
    kummerRatioHom hμ α hα = kummerRatioHom hμ β hβ := by
  have hmem : (β / α) ^ n = 1 := by
    rw [div_pow, hβ, hα, div_self']
  let ζ : rootsOfUnity n L := ⟨β / α, hmem⟩
  have hζ : β = (ζ : Lˣ) * α := by
    dsimp only [ζ]
    exact (div_mul_cancel β α).symm
  exact (kummerRatioHom_eq_of_root_mul hμ hα hβ ζ hζ).symm

/-- The Kummer homomorphism is multiplicative in the chosen root. -/
theorem kummerRatioHom_mul_roots
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a b : Kˣ} {α β : Lˣ}
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom b)
    (hαβ : (α * β) ^ n = Units.map (algebraMap K L).toMonoidHom (a * b)) :
    kummerRatioHom hμ (α * β) hαβ =
      kummerRatioHom hμ α hα * kummerRatioHom hμ β hβ := by
  apply MonoidHom.ext
  intro σ
  rw [kummerRatioHom_apply]
  change kummerRatio (α * β) hαβ σ = kummerRatio α hα σ * kummerRatio β hβ σ
  apply Subtype.ext
  rw [Subgroup.coe_mul, kummerRatio_coe_units, kummerRatio_coe_units,
    kummerRatio_coe_units, map_mul, div_mul_div_comm]

/-- The Kummer map from the subgroup of `n`-th powers from `L` to
`Hom(Gal(L/K), μ_n(L))`.  The value on a subgroup element is defined by choosing
an `n`-th root; `kummerRatioHom_eq_of_pow_eq` shows that this choice is
irrelevant. -/
noncomputable def kummerMap
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L)) :
    kummerRootSubgroup (K := K) (L := L) (n := n) →*
      ((L ≃ₐ[K] L) →* rootsOfUnity n L) where
  toFun a :=
    kummerRatioHom hμ (Classical.choose a.2) (Classical.choose_spec a.2)
  map_one' := by
    have hone : (1 : Lˣ) ^ n =
        Units.map (algebraMap K L).toMonoidHom
          ((1 : kummerRootSubgroup (K := K) (L := L) (n := n)) : Kˣ) := by
      simp
    have hEq : kummerRatioHom hμ
          (Classical.choose (1 : kummerRootSubgroup (K := K) (L := L) (n := n)).2)
          (Classical.choose_spec (1 : kummerRootSubgroup (K := K) (L := L) (n := n)).2) =
        kummerRatioHom hμ (1 : Lˣ) hone :=
      kummerRatioHom_eq_of_pow_eq hμ
        (Classical.choose_spec (1 : kummerRootSubgroup (K := K) (L := L) (n := n)).2)
        hone
    have htriv : kummerRatioHom hμ (1 : Lˣ) hone = 1 := by
      apply MonoidHom.ext
      intro σ
      apply Subtype.ext
      rw [kummerRatioHom_apply, kummerRatio_coe_units]
      simp
    exact hEq.trans htriv
  map_mul' a b := by
    have hα : (Classical.choose a.2) ^ n =
        Units.map (algebraMap K L).toMonoidHom (a : Kˣ) :=
      Classical.choose_spec a.2
    have hβ : (Classical.choose b.2) ^ n =
        Units.map (algebraMap K L).toMonoidHom (b : Kˣ) :=
      Classical.choose_spec b.2
    have hγ : (Classical.choose (a * b).2) ^ n =
        Units.map (algebraMap K L).toMonoidHom
          ((a * b : kummerRootSubgroup (K := K) (L := L) (n := n)) : Kˣ) :=
      Classical.choose_spec (a * b).2
    have hcast :
        ((a * b : kummerRootSubgroup (K := K) (L := L) (n := n)) : Kˣ) =
          (a : Kˣ) * (b : Kˣ) := rfl
    have hαβ : (Classical.choose a.2 * Classical.choose b.2) ^ n =
        Units.map (algebraMap K L).toMonoidHom
          ((a * b : kummerRootSubgroup (K := K) (L := L) (n := n)) : Kˣ) := by
      rw [mul_pow, hα, hβ, hcast, map_mul]
    have hstep1 : kummerRatioHom hμ (Classical.choose (a * b).2)
          (Classical.choose_spec (a * b).2) =
        kummerRatioHom hμ (Classical.choose a.2 * Classical.choose b.2) hαβ :=
      kummerRatioHom_eq_of_pow_eq hμ (Classical.choose_spec (a * b).2) hαβ
    have hstep2 : kummerRatioHom hμ (Classical.choose a.2 * Classical.choose b.2) hαβ =
        kummerRatioHom hμ (Classical.choose a.2) hα *
          kummerRatioHom hμ (Classical.choose b.2) hβ :=
      kummerRatioHom_mul_roots hμ hα hβ hαβ
    exact hstep1.trans hstep2

/-- The defining property of `kummerMap`: it is computed by `kummerRatioHom` on
any chosen root. -/
theorem kummerMap_apply_choose
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    (a : kummerRootSubgroup (K := K) (L := L) (n := n)) :
    kummerMap hμ a =
      kummerRatioHom hμ (Classical.choose a.2) (Classical.choose_spec a.2) := rfl

variable [FiniteDimensional K L] [IsGalois K L]

/-- If the Kummer homomorphism is trivial, then the value `a` is an `n`-th
power in `Kˣ`.  The root `α` is fixed by the whole Galois group, hence lies in
the image of `K`. -/
theorem kummer_pow_mem_of_trivial
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (htriv : ∀ σ : L ≃ₐ[K] L, kummerRatioHom hμ α hα σ = 1) :
    ∃ b : Kˣ, b ^ n = a := by
  have hfixed : ∀ σ : L ≃ₐ[K] L, σ (α : L) = (α : L) :=
    (kummerRatioHom_eq_one_iff hμ α hα).mp htriv
  have hbot : (α : L) ∈ (⊥ : IntermediateField K L) := by
    rw [IsGalois.mem_bot_iff_fixed]
    exact hfixed
  rw [IntermediateField.mem_bot] at hbot
  obtain ⟨b, hb⟩ := hbot
  have hbne : b ≠ 0 := by
    intro hb0
    have hα0 : (α : L) = 0 := by rw [← hb, hb0, map_zero]
    exact α.ne_zero hα0
  refine ⟨Units.mk0 b hbne, ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  apply FaithfulSMul.algebraMap_injective K L
  rw [map_pow, hb]
  have hcoe : ((α : Lˣ) : L) ^ n = algebraMap K L (a : K) := by
    have := congrArg (fun u : Lˣ => (u : L)) hα
    simpa using this
  exact hcoe

/-- The kernel of the Kummer map consists exactly of the `n`-th powers in
`Kˣ`. -/
theorem kummerMap_eq_one_iff
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    (a : kummerRootSubgroup (K := K) (L := L) (n := n)) :
    kummerMap hμ a = 1 ↔ ∃ b : Kˣ, b ^ n = (a : Kˣ) := by
  constructor
  · intro h
    have hα : (Classical.choose a.2) ^ n =
        Units.map (algebraMap K L).toMonoidHom (a : Kˣ) :=
      Classical.choose_spec a.2
    have hchosen : kummerRatioHom hμ (Classical.choose a.2) hα = 1 := by
      rw [← kummerMap_apply_choose]
      exact h
    have hfixed : ∀ σ : L ≃ₐ[K] L,
        σ ((Classical.choose a.2 : Lˣ) : L) = ((Classical.choose a.2 : Lˣ) : L) :=
      (kummerRatioHom_eq_one_iff hμ (Classical.choose a.2) hα).mp
        (fun σ => by
          rw [hchosen]
          rfl)
    have hbot : ((Classical.choose a.2 : Lˣ) : L) ∈ (⊥ : IntermediateField K L) := by
      rw [IsGalois.mem_bot_iff_fixed]
      exact hfixed
    rw [IntermediateField.mem_bot] at hbot
    obtain ⟨b, hb⟩ := hbot
    have hbne : b ≠ 0 := by
      intro hb0
      have hα0 : ((Classical.choose a.2 : Lˣ) : L) = 0 := by
        rw [← hb, hb0, map_zero]
      exact (Classical.choose a.2).ne_zero hα0
    refine ⟨Units.mk0 b hbne, ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    apply FaithfulSMul.algebraMap_injective K L
    rw [map_pow, hb]
    have hcoe :
        ((Classical.choose a.2 : Lˣ) : L) ^ n = algebraMap K L ((a : Kˣ) : K) := by
      have := congrArg (fun u : Lˣ => (u : L)) hα
      simpa using this
    exact hcoe
  · rintro ⟨b, hb⟩
    have hα : (Classical.choose a.2) ^ n =
        Units.map (algebraMap K L).toMonoidHom (a : Kˣ) :=
      Classical.choose_spec a.2
    have hmapb : (Units.map (algebraMap K L).toMonoidHom b) ^ n =
        Units.map (algebraMap K L).toMonoidHom (a : Kˣ) := by
      rw [← map_pow, hb]
    have hEq : kummerRatioHom hμ (Classical.choose a.2) hα =
        kummerRatioHom hμ (Units.map (algebraMap K L).toMonoidHom b) hmapb :=
      kummerRatioHom_eq_of_pow_eq hμ hα hmapb
    rw [kummerMap_apply_choose, hEq]
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    rw [kummerRatioHom_apply, kummerRatio_coe_units]
    have hfix :
        Units.map (σ : L →* L) (Units.map (algebraMap K L).toMonoidHom b) =
          Units.map (algebraMap K L).toMonoidHom b := by
      ext
      simp [AlgEquiv.commutes]
    rw [hfix, div_self']
    rfl

end KummerGaloisClass

end LeanFormal.IUT
