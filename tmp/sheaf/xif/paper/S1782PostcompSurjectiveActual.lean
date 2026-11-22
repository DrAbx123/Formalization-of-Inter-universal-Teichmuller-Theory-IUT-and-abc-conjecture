/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.RingTheory.Etale.Field

/-!
# S1748 -- the automorphism group of the geometric fibre functor

For a field `K` and a geometric point `Ω` (an algebraic closure of `K`), Mathlib provides the
fibre functor

  `CommAlgCat.FiniteEtale.fiber K Ω : (FiniteEtale K)ᵒᵖ ⥤ FintypeCat`,  `S ↦ (S →ₐ[K] Ω)`.

The target of this file is the comparison

  `Aut (fiber K Ω) ≃* (Ω ≃ₐ[K] Ω) = Field.absoluteGaloisGroup K`.

## What is proved here (no sorry, no extra axioms)

* `postcomp` / `postcompMonoidHom`: postcomposition with a `K`-automorphism of `Ω` is a
  natural automorphism of the fibre functor, and this is a monoid homomorphism
  `(Ω ≃ₐ[K] Ω) →* Aut (fiber K Ω)`.

* `sigmaAt` and `sigmaAt_restrict`: the value of a natural automorphism `σ` on the identity
  of a finite separable intermediate field `L ⊆ Ω`; naturality says these values are compatible
  with inclusions.

* `g`, `g_eq_sigmaAt`, `g_add`, `g_mul`, `g_one`, `g_zero`, `g_commutes`, `gHom`: a
  natural automorphism of the fibre functor induces a genuine `K`-algebra map
  `separableClosure K Ω →ₐ[K] Ω`.

* `surjective_of_algHom_self`: a `K`-algebra endomorphism of an algebraic closure is
  surjective (root-set argument).

* `toAlgEquiv`, `toAlgEquiv_apply_eq`: extension of `gHom` to a `K`-automorphism of `Ω`
  (`IsAlgClosed.surjective_restrictDomain_of_isAlgebraic`).

* `algEquiv_ext_of_agree` and `toAlgEquiv_postcomp`: two `K`-automorphisms of `Ω` which agree
  on the separable closure are equal (`Ω` is purely inseparable over `separableClosure K Ω`, so
  `Ω →ₐ[separableClosure K Ω] Ω` is a subsingleton).  Hence `toAlgEquiv ∘ postcomp = id`.

* `postcomp_injective`, `toAlgEquiv_surjective`: postcomposition is injective and
  `Aut (fiber K Ω) ↠ (Ω ≃ₐ[K] Ω)` is a split surjection.

* `autFiberEquivOfSurjective`: the comparison `Aut (fiber K Ω) ≃* (Ω ≃ₐ[K] Ω)` follows from
  the single missing statement `PostcompSurjective` (see Section 10); this conditional theorem
  is fully proved.

## What is *not* proved here

* `PostcompSurjective` (`σ.app A f = (toAlgEquiv σ).comp f` for all `A`, `f`): Section 10
  records the precise mathematical content and the Mathlib inputs.
* The `PreGaloisCategory.FiberFunctor` instance for `fiber K Ω`: its statement needs
  `PreGaloisCategory (FiniteEtale K)ᵒᵖ` (quotients by finite groups = Galois descent for finite
  etale algebras, and `monoInducesIsoOnDirectSummand`), none of which is in Mathlib.

The axiom audit at the end of the file shows that every declaration proved here depends only on
`propext`, `Classical.choice` and `Quot.sound`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace S1748FiniteEtaleFiber

set_option maxHeartbeats 1000000

variable (K : Type u) [Field K]

/-- The opposite of the category of finite etale `K`-algebras: the category of finite etale
`K`-schemes (affine ones).  The fibre functor is covariant on this category. -/
abbrev C : Type (u + 1) := (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ

variable {K}

/-- The geometric fibre functor at `Ω`. -/
abbrev fiber {Ω : Type u} [Field Ω] [Algebra K Ω] : C K ⥤ FintypeCat.{u} :=
  CommAlgCat.FiniteEtale.fiber K Ω

/-! ### 1. Intermediate fields as finite etale `K`-algebras -/

namespace IntermediateField

variable {Ω : Type u} [Field Ω] [Algebra K Ω]

/-- A finite separable intermediate field of `Ω/K` is a finite etale `K`-algebra. -/
instance (L : IntermediateField K Ω) [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Algebra.Etale K L where
  formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
  finitePresentation := (Algebra.FinitePresentation.of_finiteType).mp inferInstance

/-- The corresponding object of `(FiniteEtale K)ᵒᵖ`. -/
abbrev toFiniteEtale (L : IntermediateField K Ω) [FiniteDimensional K L]
    [Algebra.IsSeparable K L] : C K :=
  Opposite.op (CommAlgCat.FiniteEtale.of K L)

end IntermediateField

/-! ### 2. Postcomposition with an automorphism of the geometric point -/

variable {Ω : Type u} [Field Ω] [Algebra K Ω]

/-- The bijection `Hom(A, Ω) ≃ Hom(A, Ω)` induced by postcomposition with a `K`-algebra
automorphism of `Ω`. -/
def postcompEquiv (h : Ω ≃ₐ[K] Ω) (A : C K) :
    (fiber (K := K) (Ω := Ω)).obj A ≃ (fiber (K := K) (Ω := Ω)).obj A where
  toFun f := h.toAlgHom.comp f
  invFun f := h.symm.toAlgHom.comp f
  left_inv f := AlgHom.ext fun x => by simp
  right_inv f := AlgHom.ext fun x => by simp

/-- Postcomposition by a `K`-algebra automorphism of `Ω` is a natural automorphism of the fibre
functor. -/
def postcomp (h : Ω ≃ₐ[K] Ω) : Aut (fiber (K := K) (Ω := Ω)) :=
  NatIso.ofComponents (fun A => FintypeCat.equivEquivIso (postcompEquiv h A)) (by
    intro A B f
    apply FintypeCat.hom_ext
    intro u
    rfl)

@[simp]
theorem postcomp_hom_app_apply (h : Ω ≃ₐ[K] Ω) (A : C K) (f : A.unop →ₐ[K] Ω) :
    (postcomp h).hom.app A f = h.toAlgHom.comp f := rfl

/-- Postcomposition is a group homomorphism from the absolute Galois group into the automorphism
group of the fibre functor. -/
def postcompMonoidHom : (Ω ≃ₐ[K] Ω) →* Aut (fiber (K := K) (Ω := Ω)) where
  toFun := postcomp
  map_one' := by
    ext A f
    rfl
  map_mul' h₁ h₂ := by
    ext A f
    rfl

@[simp]
theorem postcompMonoidHom_apply (h : Ω ≃ₐ[K] Ω) : postcompMonoidHom h = postcomp h := rfl

/-! ### 3. The value of a natural automorphism on finite separable subfields -/

section Values

variable {Ω : Type u} [Field Ω] [Algebra K Ω]

/-- The `K`-algebra map `L → Ω` obtained by applying a natural automorphism `σ` of the fibre
functor to the identity embedding of a finite separable intermediate field `L`. -/
def sigmaAt (σ : Aut (fiber (K := K) (Ω := Ω))) (L : IntermediateField K Ω)
    [FiniteDimensional K L] [Algebra.IsSeparable K L] : ↥L →ₐ[K] Ω :=
  σ.hom.app (IntermediateField.toFiniteEtale L) (IntermediateField.val L)

variable {σ : Aut (fiber (K := K) (Ω := Ω))}

/-- The maps `sigmaAt σ L` are compatible with inclusions of finite separable intermediate
fields: this is the naturality of `σ`. -/
theorem sigmaAt_restrict {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [FiniteDimensional K L'] [Algebra.IsSeparable K L']
    (h : L ≤ L') (x : ↥L) :
    sigmaAt σ L x = sigmaAt σ L' ⟨x.1, h x.2⟩ := by
  have hnat := congrArg (fun k : (fiber (K := K) (Ω := Ω)).obj (IntermediateField.toFiniteEtale L') ⟶
      (fiber (K := K) (Ω := Ω)).obj (IntermediateField.toFiniteEtale L) =>
      k (IntermediateField.val L' : ↥L' →ₐ[K] Ω))
    (NatTrans.naturality σ.hom (f := (CommAlgCat.FiniteEtale.ofHom (IntermediateField.inclusion h)).op))
  exact congrArg (fun g : ↥L →ₐ[K] Ω => g x) hnat

end Values

/-! ### 4. The induced map on the separable closure -/

/-- The union of all finite separable subextensions of `Ω/K` is the separable closure. -/
theorem le_separableClosure_of_finiteDimensional (L : IntermediateField K Ω)
    [FiniteDimensional K L] [Algebra.IsSeparable K L] : L ≤ separableClosure K Ω :=
  le_separableClosure K Ω L

/-- The image of a separable element under a natural automorphism of the fibre functor. -/
noncomputable def g (σ : Aut (fiber (K := K) (Ω := Ω))) (x : ↥(separableClosure K Ω)) : Ω :=
  haveI : FiniteDimensional K ↥(IntermediateField.adjoin K {(x : Ω)}) :=
    IntermediateField.adjoin.finiteDimensional (mem_separableClosure_iff.mp x.2).isIntegral
  haveI : Algebra.IsSeparable K ↥(IntermediateField.adjoin K {(x : Ω)}) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable (F := K) (E := Ω) (S := {(x : Ω)})).mpr (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      simpa using mem_separableClosure_iff.mp x.2)
  sigmaAt σ (IntermediateField.adjoin K {(x : Ω)})
    ⟨(x : Ω), IntermediateField.mem_adjoin_simple_self K (x : Ω)⟩

/-- `g` is computed by `sigmaAt` on every finite separable intermediate field. -/
theorem g_eq_sigmaAt (σ : Aut (fiber (K := K) (Ω := Ω))) {L : IntermediateField K Ω}
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (z : ↥L) :
    g σ ⟨z.1, le_separableClosure K Ω L z.2⟩ = sigmaAt σ L z := by
  haveI : FiniteDimensional K ↥(IntermediateField.adjoin K {(z : Ω)}) :=
    IntermediateField.adjoin.finiteDimensional (mem_separableClosure_iff.mp (le_separableClosure K Ω L z.2)).isIntegral
  haveI : Algebra.IsSeparable K ↥(IntermediateField.adjoin K {(z : Ω)}) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable (F := K) (E := Ω) (S := {(z : Ω)})).mpr (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact mem_separableClosure_iff.mp (le_separableClosure K Ω L z.2))
  have hle : IntermediateField.adjoin K {(z : Ω)} ≤ L := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact z.2
  have h := sigmaAt_restrict (σ := σ) (L := IntermediateField.adjoin K {(z : Ω)}) (L' := L) hle
    ⟨(z : Ω), IntermediateField.mem_adjoin_simple_self K (z : Ω)⟩
  simpa [g] using h

/-! ### 5. `g` is a `K`-algebra homomorphism -/

section AlgHom

variable {Ω : Type u} [Field Ω] [Algebra K Ω]

/-- `K(x, y)` is finite over `K` when `x` and `y` are integral over `K`. -/
theorem finiteDimensional_adjoin_pair {x y : Ω} (hx : IsIntegral K x) (hy : IsIntegral K y) :
    FiniteDimensional K ↥(IntermediateField.adjoin K ({x, y} : Set Ω)) := by
  apply IntermediateField.finiteDimensional_adjoin
  intro z hz
  rcases Set.mem_insert_iff.mp hz with h | h
  · subst h; exact hx
  · rw [Set.mem_singleton_iff] at h; subst h; exact hy

/-- `K(x, y)` is separable over `K` when `x` and `y` are. -/
theorem isSeparable_adjoin_pair {x y : Ω} (hx : IsSeparable K x) (hy : IsSeparable K y) :
    Algebra.IsSeparable K ↥(IntermediateField.adjoin K ({x, y} : Set Ω)) := by
  rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
  intro z hz
  rcases Set.mem_insert_iff.mp hz with h | h
  · subst h; exact hx
  · rw [Set.mem_singleton_iff] at h; subst h; exact hy

/-- The first generator lies in the compositum. -/
theorem mem_adjoin_pair {x y : Ω} : x ∈ IntermediateField.adjoin K ({x, y} : Set Ω) :=
  IntermediateField.subset_adjoin K ({x, y} : Set Ω) (by simp)

/-- The second generator lies in the compositum. -/
theorem mem_adjoin_pair' {x y : Ω} : y ∈ IntermediateField.adjoin K ({x, y} : Set Ω) :=
  IntermediateField.subset_adjoin K ({x, y} : Set Ω) (by simp)

variable (σ : Aut (fiber (K := K) (Ω := Ω)))

/-- `g` agrees with `sigmaAt` at every element of a finite separable intermediate field. -/
theorem g_apply_eq {L : IntermediateField K Ω} [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (z : ↥(separableClosure K Ω)) (hz : (z : Ω) ∈ L) :
    g σ z = sigmaAt σ L ⟨(z : Ω), hz⟩ :=
  g_eq_sigmaAt σ (⟨(z : Ω), hz⟩ : ↥L)

/-- `g` is additive. -/
theorem g_add (x y : ↥(separableClosure K Ω)) : g σ (x + y) = g σ x + g σ y := by
  have hx : IsSeparable K (x : Ω) := mem_separableClosure_iff.mp x.2
  have hy : IsSeparable K (y : Ω) := mem_separableClosure_iff.mp y.2
  haveI hfin : FiniteDimensional K ↥(IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω)) :=
    finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  haveI hsep : Algebra.IsSeparable K ↥(IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω)) :=
    isSeparable_adjoin_pair hx hy
  have hxL : (x : Ω) ∈ IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω) := mem_adjoin_pair
  have hyL : (y : Ω) ∈ IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω) := mem_adjoin_pair'
  have hxyL : ((x + y : ↥(separableClosure K Ω)) : Ω) ∈
      IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω) := by
    rw [show ((x + y : ↥(separableClosure K Ω)) : Ω) = (x : Ω) + (y : Ω) from rfl]
    exact add_mem hxL hyL
  rw [g_apply_eq σ x hxL, g_apply_eq σ y hyL, g_apply_eq σ (x + y) hxyL,
    show (⟨((x + y : ↥(separableClosure K Ω)) : Ω), hxyL⟩ :
        ↥(IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω))) =
      (⟨(x : Ω), hxL⟩ : ↥(IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω))) +
        ⟨(y : Ω), hyL⟩ from rfl,
    map_add]

/-- `g` is multiplicative. -/
theorem g_mul (x y : ↥(separableClosure K Ω)) : g σ (x * y) = g σ x * g σ y := by
  have hx : IsSeparable K (x : Ω) := mem_separableClosure_iff.mp x.2
  have hy : IsSeparable K (y : Ω) := mem_separableClosure_iff.mp y.2
  haveI hfin : FiniteDimensional K ↥(IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω)) :=
    finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
  haveI hsep : Algebra.IsSeparable K ↥(IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω)) :=
    isSeparable_adjoin_pair hx hy
  have hxL : (x : Ω) ∈ IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω) := mem_adjoin_pair
  have hyL : (y : Ω) ∈ IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω) := mem_adjoin_pair'
  have hxyL : ((x * y : ↥(separableClosure K Ω)) : Ω) ∈
      IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω) := by
    rw [show ((x * y : ↥(separableClosure K Ω)) : Ω) = (x : Ω) * (y : Ω) from rfl]
    exact mul_mem hxL hyL
  rw [g_apply_eq σ x hxL, g_apply_eq σ y hyL, g_apply_eq σ (x * y) hxyL,
    show (⟨((x * y : ↥(separableClosure K Ω)) : Ω), hxyL⟩ :
        ↥(IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω))) =
      (⟨(x : Ω), hxL⟩ : ↥(IntermediateField.adjoin K ({(x : Ω), (y : Ω)} : Set Ω))) *
        ⟨(y : Ω), hyL⟩ from rfl,
    map_mul]

/-- `g` sends `1` to `1`. -/
theorem g_one : g σ (1 : ↥(separableClosure K Ω)) = 1 := by
  have h1 : IsSeparable K (1 : Ω) := mem_separableClosure_iff.mp (1 : ↥(separableClosure K Ω)).2
  haveI hfin : FiniteDimensional K ↥(IntermediateField.adjoin K ({(1 : Ω), (1 : Ω)} : Set Ω)) :=
    finiteDimensional_adjoin_pair h1.isIntegral h1.isIntegral
  haveI hsep : Algebra.IsSeparable K ↥(IntermediateField.adjoin K ({(1 : Ω), (1 : Ω)} : Set Ω)) :=
    isSeparable_adjoin_pair h1 h1
  have hL : (1 : Ω) ∈ IntermediateField.adjoin K ({(1 : Ω), (1 : Ω)} : Set Ω) := mem_adjoin_pair
  rw [g_apply_eq σ 1 hL]
  exact map_one _

/-- `g` sends `0` to `0`. -/
theorem g_zero : g σ (0 : ↥(separableClosure K Ω)) = 0 := by
  have h1 : IsSeparable K (0 : Ω) := mem_separableClosure_iff.mp (0 : ↥(separableClosure K Ω)).2
  haveI hfin : FiniteDimensional K ↥(IntermediateField.adjoin K ({(0 : Ω), (0 : Ω)} : Set Ω)) :=
    finiteDimensional_adjoin_pair h1.isIntegral h1.isIntegral
  haveI hsep : Algebra.IsSeparable K ↥(IntermediateField.adjoin K ({(0 : Ω), (0 : Ω)} : Set Ω)) :=
    isSeparable_adjoin_pair h1 h1
  have hL : (0 : Ω) ∈ IntermediateField.adjoin K ({(0 : Ω), (0 : Ω)} : Set Ω) := mem_adjoin_pair
  rw [g_apply_eq σ 0 hL]
  exact map_zero _

/-- `g` is `K`-linear. -/
theorem g_commutes (k : K) :
    g σ (algebraMap K ↥(separableClosure K Ω) k) = algebraMap K Ω k := by
  have h1 : IsSeparable K (algebraMap K Ω k) :=
    mem_separableClosure_iff.mp (algebraMap K ↥(separableClosure K Ω) k).2
  haveI hfin : FiniteDimensional K
      ↥(IntermediateField.adjoin K ({(algebraMap K Ω k), (algebraMap K Ω k)} : Set Ω)) :=
    finiteDimensional_adjoin_pair h1.isIntegral h1.isIntegral
  haveI hsep : Algebra.IsSeparable K
      ↥(IntermediateField.adjoin K ({(algebraMap K Ω k), (algebraMap K Ω k)} : Set Ω)) :=
    isSeparable_adjoin_pair h1 h1
  have hL : algebraMap K Ω k ∈
      IntermediateField.adjoin K ({(algebraMap K Ω k), (algebraMap K Ω k)} : Set Ω) := mem_adjoin_pair
  rw [g_apply_eq σ _ hL]
  exact AlgHom.commutes _ k

/-- A natural automorphism of the fibre functor induces a `K`-algebra map from the separable
closure of `K` in `Ω` to `Ω`. -/
noncomputable def gHom : ↥(separableClosure K Ω) →ₐ[K] Ω where
  toFun := g σ
  map_one' := g_one σ
  map_zero' := g_zero σ
  map_add' := g_add σ
  map_mul' := g_mul σ
  commutes' := g_commutes σ

end AlgHom

/-! ### 6. From a natural automorphism to an automorphism of the algebraic closure -/

section Extension

variable [IsAlgClosure K Ω]

/-- A `K`-algebra endomorphism of an algebraic closure of `K` is surjective.

Indeed, for `x : Ω` the minimal polynomial `p` of `x` over `K` is non-zero, its root set in `Ω`
is finite, and `φ` maps this finite set injectively to itself; hence `x` is a value of `φ`. -/
theorem surjective_of_algHom_self (φ : Ω →ₐ[K] Ω) : Function.Surjective φ := by
  classical
  intro x
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hp : minpoly K x ≠ 0 := minpoly.ne_zero hx
  have hpmap : (minpoly K x).map (algebraMap K Ω) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K Ω).injective).mpr hp
  set s : Finset Ω := ((minpoly K x).map (algebraMap K Ω)).roots.toFinset with hs
  have hxs : x ∈ s := by
    rw [hs, Multiset.mem_toFinset, Polynomial.mem_roots hpmap, Polynomial.IsRoot.def]
    have h := minpoly.aeval K x
    rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at h
  have hmap : ∀ y ∈ s, φ y ∈ s := by
    intro y hy
    rw [hs, Multiset.mem_toFinset, Polynomial.mem_roots hpmap, Polynomial.IsRoot.def] at hy ⊢
    have hy' : Polynomial.aeval y (minpoly K x) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact hy
    have h2 : Polynomial.aeval (φ y) (minpoly K x) = 0 := by
      rw [Polynomial.aeval_algHom_apply, hy', map_zero]
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at h2
    exact h2
  have hinj : Set.InjOn φ ↑s := fun a _ b _ hab => φ.injective hab
  have hcard : (s.image φ).card = s.card := Finset.card_image_of_injOn hinj
  have hsub : s.image φ ⊆ s := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact hmap z hz
  have heq : s.image φ = s := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have hx' : x ∈ s.image φ := heq.symm ▸ hxs
  obtain ⟨y, _, hyx⟩ := Finset.mem_image.mp hx'
  exact ⟨y, hyx⟩

/-- A natural automorphism of the fibre functor is induced by a `K`-algebra automorphism of the
algebraic closure: the map `g` on the separable closure extends to `Ω`. -/
noncomputable def toAlgEquiv (σ : Aut (fiber (K := K) (Ω := Ω))) : Ω ≃ₐ[K] Ω :=
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hex : ∃ f : Ω →ₐ[K] Ω,
      f.restrictDomain ↥(separableClosure K Ω) = gHom σ :=
    IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := K)
      (L := ↥(separableClosure K Ω)) (M := Ω) (E := Ω) (gHom σ)
  let f : Ω →ₐ[K] Ω := Classical.choose hex
  have hf : f.restrictDomain ↥(separableClosure K Ω) = gHom σ := Classical.choose_spec hex
  AlgEquiv.ofBijective f ⟨f.injective, surjective_of_algHom_self f⟩

/-- The automorphism constructed from `σ` restricts to `g` on the separable closure. -/
theorem toAlgEquiv_apply_eq (σ : Aut (fiber (K := K) (Ω := Ω)))
    (y : ↥(separableClosure K Ω)) : toAlgEquiv σ y = gHom σ y := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hex : ∃ f : Ω →ₐ[K] Ω,
      f.restrictDomain ↥(separableClosure K Ω) = gHom σ :=
    IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := K)
      (L := ↥(separableClosure K Ω)) (M := Ω) (E := Ω) (gHom σ)
  have hf : (Classical.choose hex).restrictDomain ↥(separableClosure K Ω) = gHom σ :=
    Classical.choose_spec hex
  show (AlgEquiv.ofBijective (Classical.choose hex) _) y = gHom σ y
  exact AlgHom.congr_fun hf y

end Extension

/-! ### 7. Round trip: postcomposition is injective -/

section RoundTrip

variable [IsAlgClosure K Ω]

/-- On the separable closure, `g` of a postcomposition is the postcomposition itself. -/
theorem g_postcomp (h : Ω ≃ₐ[K] Ω) (x : ↥(separableClosure K Ω)) :
    g (postcomp h) x = h x := by
  have hx : IsSeparable K (x : Ω) := mem_separableClosure_iff.mp x.2
  haveI hfin : FiniteDimensional K ↥(IntermediateField.adjoin K {(x : Ω)}) :=
    IntermediateField.adjoin.finiteDimensional hx.isIntegral
  haveI hsep : Algebra.IsSeparable K ↥(IntermediateField.adjoin K {(x : Ω)}) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable (F := K) (E := Ω) (S := {(x : Ω)})).mpr (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hx)
  have hmem : (x : Ω) ∈ IntermediateField.adjoin K {(x : Ω)} :=
    IntermediateField.mem_adjoin_simple_self K (x : Ω)
  rw [g_apply_eq (postcomp h) x hmem]
  simp only [sigmaAt, postcomp_hom_app_apply]
  rfl

/-- Two `K`-automorphisms of an algebraic closure of `K` which agree on the separable closure
are equal: `Ω` is purely inseparable over its separable closure. -/
theorem algEquiv_ext_of_agree (f g : Ω ≃ₐ[K] Ω)
    (h : ∀ y : ↥(separableClosure K Ω), f y = g y) : f = g := by
  haveI hpi : IsPurelyInseparable ↥(separableClosure K Ω) Ω := inferInstance
  have key : ∀ y : ↥(separableClosure K Ω), (g.trans f.symm) (y : Ω) = (y : Ω) := by
    intro y
    rw [AlgEquiv.trans_apply, ← h y, AlgEquiv.symm_apply_apply]
  let e' : Ω →ₐ[↥(separableClosure K Ω)] Ω :=
    { toFun := ⇑(g.trans f.symm)
      map_one' := map_one _
      map_mul' := map_mul _
      map_zero' := map_zero _
      map_add' := map_add _
      commutes' := fun s => key s }
  have he : e' = AlgHom.id ↥(separableClosure K Ω) Ω := Subsingleton.elim _ _
  ext y
  have h2 : (g.trans f.symm) y = y := by
    have h3 := congrArg (fun k : Ω →ₐ[↥(separableClosure K Ω)] Ω => (k : Ω → Ω) y) he
    simpa [e'] using h3
  rw [AlgEquiv.trans_apply] at h2
  have h4 : g y = f y := by
    have := congrArg (⇑f) h2
    simpa using this
  exact h4.symm

/-- The composite `σ ↦ toAlgEquiv σ` after postcomposition is the identity: postcomposition is
injective on `K`-automorphisms of the algebraic closure. -/
theorem toAlgEquiv_postcomp (h : Ω ≃ₐ[K] Ω) : toAlgEquiv (postcomp h) = h :=
  algEquiv_ext_of_agree (toAlgEquiv (postcomp h)) h (fun y => by
    rw [toAlgEquiv_apply_eq]
    exact g_postcomp h y)

/-- Postcomposition with a `K`-automorphism of `Ω` is an injective map. -/
theorem postcomp_injective : Function.Injective (postcomp (K := K) (Ω := Ω)) := by
  intro h₁ h₂ h12
  have := congrArg (toAlgEquiv (K := K) (Ω := Ω)) h12
  simpa [toAlgEquiv_postcomp] using this

end RoundTrip



/-! ### 8. Exact remaining gap: surjectivity of postcomposition -/

section Remaining

variable [IsAlgClosure K Ω]

/-- The precise statement that is still missing for the full comparison: every natural
automorphism of the geometric fibre functor is the postcomposition with a `K`-automorphism of
`Ω`.  This is a proposition, not an assertion: it is *not* proved in this file. -/
def PostcompSurjective : Prop := Function.Surjective (postcomp (K := K) (Ω := Ω))

/-- The conditional comparison: if postcomposition is surjective, then the automorphism group of
the geometric fibre functor is the absolute Galois group.  Both directions are proved here (the
injectivity is `postcomp_injective`); only `h` is missing. -/
noncomputable def autFiberEquivOfSurjective (h : PostcompSurjective (K := K) (Ω := Ω)) :
    Aut (fiber (K := K) (Ω := Ω)) ≃* (Ω ≃ₐ[K] Ω) :=
  (MulEquiv.ofBijective (postcompMonoidHom (K := K) (Ω := Ω))
    ⟨postcomp_injective, h⟩).symm

/-- Unconditionally, the automorphism group of the fibre functor *surjects* onto the absolute
Galois group via `toAlgEquiv`; postcomposition is a section of this surjection. -/
theorem toAlgEquiv_surjective : Function.Surjective (toAlgEquiv (K := K) (Ω := Ω)) :=
  fun h => ⟨postcomp h, toAlgEquiv_postcomp h⟩

/-- Unconditionally, distinct `K`-automorphisms of `Ω` induce distinct natural automorphisms of
the geometric fibre functor. -/
theorem postcomp_injective' : Function.Injective (postcomp (K := K) (Ω := Ω)) :=
  postcomp_injective

end Remaining

/-! ### 9. Specialisation to the algebraic closure -/

section Absolute

/-- The geometric fibre functor at the algebraic closure of `K`. -/
abbrev absoluteFiber : C K ⥤ FintypeCat.{u} :=
  fiber (K := K) (Ω := AlgebraicClosure K)

/-- The absolute Galois group injects into the automorphism group of the geometric fibre functor
at an algebraic closure. -/
theorem postcomp_absoluteGaloisGroup_injective :
    Function.Injective (postcomp (K := K) (Ω := AlgebraicClosure K)) :=
  postcomp_injective

/-- Every `K`-automorphism of `AlgebraicClosure K` is recovered from its action on the fibre
functor: the retraction `toAlgEquiv` of postcomposition is surjective onto
`Field.absoluteGaloisGroup K`. -/
theorem toAlgEquiv_absolute_surjective :
    Function.Surjective (toAlgEquiv (K := K) (Ω := AlgebraicClosure K)) :=
  fun h => ⟨postcomp h, toAlgEquiv_postcomp h⟩

end Absolute

/-! ### 10. What is missing, precisely

The single missing input for the unconditional statement
`Aut (fiber K Ω) ≃* (Ω ≃ₐ[K] Ω)` is `PostcompSurjective`: for every `σ : Aut (fiber K Ω)`,
every finite etale `K`-algebra `A` and every `f : A →ₐ[K] Ω`,

  `σ.app A f = (toAlgEquiv σ).comp f`.

The proof reduces to two inputs, both available in Mathlib but not yet assembled here:

1. `Algebra.Etale.iff_exists_algEquiv_prod` (`Mathlib/RingTheory/Etale/Field.lean`): a finite
   etale `K`-algebra is a finite product of finite separable field extensions.  It implies that
   the image of `f` is a finite separable subextension of `Ω`, i.e. lies in the separable
   closure `separableClosure K Ω`, where `toAlgEquiv σ` is known to agree with `σ`
   (`toAlgEquiv_apply_eq`).

2. The factorization: a `K`-algebra map from a finite product of fields into a field factors
   through exactly one projection (`exists_comp_evalAlgHom`-type statement), and a map out of a
   product is determined by its restrictions to the factors.

Given these, naturality of `σ` along the projection `A → f.range` (a morphism of finite etale
`K`-algebras after 1) identifies `σ.app A f` with `(toAlgEquiv σ).comp f`, which is exactly
`PostcompSurjective`.

The `PreGaloisCategory.FiberFunctor` instance for `fiber K Ω` is *not* addressed in this file:
its very statement requires `PreGaloisCategory (FiniteEtale K)ᵒᵖ`, which in turn requires
quotients by finite groups (fixed points of finite etale algebras, i.e. Galois descent) and
`monoInducesIsoOnDirectSummand` (epimorphisms of finite etale algebras are projections of a
product); neither is in Mathlib.
-/

/-!
### 11. Axiom audit
-/

#print axioms S1748FiniteEtaleFiber.postcompMonoidHom
#print axioms S1748FiniteEtaleFiber.sigmaAt_restrict
#print axioms S1748FiniteEtaleFiber.g_eq_sigmaAt
#print axioms S1748FiniteEtaleFiber.gHom
#print axioms S1748FiniteEtaleFiber.surjective_of_algHom_self
#print axioms S1748FiniteEtaleFiber.toAlgEquiv
#print axioms S1748FiniteEtaleFiber.toAlgEquiv_apply_eq
#print axioms S1748FiniteEtaleFiber.g_postcomp
#print axioms S1748FiniteEtaleFiber.algEquiv_ext_of_agree
#print axioms S1748FiniteEtaleFiber.toAlgEquiv_postcomp
#print axioms S1748FiniteEtaleFiber.postcomp_injective
#print axioms S1748FiniteEtaleFiber.toAlgEquiv_surjective
#print axioms S1748FiniteEtaleFiber.autFiberEquivOfSurjective

end S1748FiniteEtaleFiber

/-!
### S1782: surjectivity of postcomposition --- the missing `PostcompSurjective`

Let `K` be a field, `Ω` an algebraic closure of `K`, and `σ` a natural automorphism of the
geometric fibre functor `A ↦ (A →ₐ[K] Ω)` on finite étale `K`-algebras.  This file supplies the
step that S1748 left open:

  `σ.hom.app A f = (toAlgEquiv σ).comp f`  for every finite étale `A` and every `f : A →ₐ[K] Ω`.

Ingredients:

* `Algebra.Etale.iff_exists_algEquiv_prod`: `A ≃ₐ[K] ∏ i, L i` with each `L i` a finite
  separable field extension of `K`.
* `exists_comp_evalAlgHom`: a `K`-algebra map from a finite product of fields into a field
  factors through exactly one projection (idempotent argument on `Pi.single i 1`).
* `app_of_field`: for a finite separable field `L` and `φ : L →ₐ[K] Ω`, naturality along
  `L → φ.fieldRange` and `toAlgEquiv_comp_val` identify `σ` with `toAlgEquiv σ`.

Assembled in `app_eq_comp`; `postcompSurjective` and `autFiberEquiv` then give the
unconditional comparison `Aut (fiber K Ω) ≃* (Ω ≃ₐ[K] Ω)`.
-/

namespace S1782PostcompSurjective

open S1748FiniteEtaleFiber

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω]

/-! #### 1. Naturality on an arbitrary morphism -/

variable {σ : Aut (fiber (K := K) (Ω := Ω))}

/-- Naturality of `σ`: for `g : S →ₐ[K] T` and `h : T →ₐ[K] Ω`,
`σ.app S (h ∘ g) = (σ.app T h) ∘ g`. -/
theorem app_comp {S T : CommAlgCat.FiniteEtale.{u} K} (g : S →ₐ[K] T) (h : T →ₐ[K] Ω) :
    σ.hom.app (Opposite.op S) (h.comp g) = (σ.hom.app (Opposite.op T) h).comp g := by
  let hφ : S ⟶ T := InducedCategory.homMk (X := S) (Y := T) (CommAlgCat.ofHom g)
  exact congrArg
    (fun k : (fiber (K := K) (Ω := Ω)).obj (Opposite.op T) ⟶
        (fiber (K := K) (Ω := Ω)).obj (Opposite.op S) => k h)
    (NatTrans.naturality σ.hom (f := hφ.op))

/-! #### 2. `toAlgEquiv` agrees with `sigmaAt` on finite separable subfields -/

/-- On a finite separable intermediate field, `toAlgEquiv σ` coincides with `sigmaAt σ L`. -/
theorem toAlgEquiv_comp_val [IsAlgClosure K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    (toAlgEquiv σ).toAlgHom.comp (IntermediateField.val L) = sigmaAt σ L := by
  ext z
  show toAlgEquiv σ (z : Ω) = sigmaAt σ L z
  rw [toAlgEquiv_apply_eq σ ⟨(z : Ω), le_separableClosure K Ω L z.2⟩]
  exact g_eq_sigmaAt σ z

/-! #### 3. A map from a finite product of fields into a field factors through a projection -/

/-- A `K`-algebra map from a finite product of fields into a field factors through one of the
projections. -/
theorem exists_comp_evalAlgHom {ι : Type u} [Fintype ι] [DecidableEq ι]
    (L : ι → Type u) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    (F : (Π i, L i) →ₐ[K] Ω) :
    ∃ (j : ι) (G : L j →ₐ[K] Ω), F = G.comp (Pi.evalAlgHom K L j) := by
  classical
  have hidem : ∀ i, F (Pi.single i (1 : L i)) = 0 ∨ F (Pi.single i (1 : L i)) = 1 := by
    intro i
    have hmul : F (Pi.single i (1 : L i)) * F (Pi.single i (1 : L i)) = F (Pi.single i (1 : L i)) := by
      rw [← map_mul, ← Pi.single_mul, one_mul]
    have h0 : F (Pi.single i (1 : L i)) * (F (Pi.single i (1 : L i)) - 1) = 0 := by
      rw [mul_sub, hmul, mul_one, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hsum : (∑ i, F (Pi.single i (1 : L i))) = 1 := by
    have h1 : (∑ i, (Pi.single i (1 : L i) : Π i, L i)) = 1 :=
      Finset.univ_sum_single (fun i => (1 : L i))
    rw [← map_sum, h1, map_one]
  obtain ⟨j, hj⟩ : ∃ j, F (Pi.single j (1 : L j)) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    rw [Finset.sum_eq_zero (fun i _ => h i)] at hsum
    exact zero_ne_one hsum
  have hj1 : F (Pi.single j (1 : L j)) = 1 := (hidem j).resolve_left hj
  let G : L j →ₐ[K] Ω :=
    { toFun := fun x => F (Pi.single j x)
      map_one' := by simpa using hj1
      map_mul' := fun x y => by rw [Pi.single_mul, map_mul]
      map_zero' := by rw [Pi.single_zero, map_zero]
      map_add' := fun x y => by rw [Pi.single_add, map_add]
      commutes' := fun k => by
        have h1 : (Pi.single j (algebraMap K (L j) k) : Π i, L i) =
            Pi.single j (1 : L j) * algebraMap K (Π i, L i) k := by
          ext i
          by_cases h : i = j
          · subst h; simp
          · simp [h]
        rw [h1, map_mul, hj1, one_mul, AlgHom.commutes] }
  refine ⟨j, G, ?_⟩
  ext y
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply]
  show F y = F (Pi.single j (y j))
  have h1 : (Pi.single j (1 : L j) * y : Π i, L i) = Pi.single j (y j) := by
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [← h1, map_mul, hj1, one_mul]

/-! #### 4. Finite separable field extensions are étale -/

/-- A field which is finite and separable over `K` is a finite étale `K`-algebra. -/
theorem etale_of_finite_separable (L : Type u) [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] : Algebra.Etale K L where
  formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
  finitePresentation := (Algebra.FinitePresentation.of_finiteType).mp inferInstance

/-! #### 5. The field case -/

/-- If `L` is a finite separable field extension of `K` and `φ : L →ₐ[K] Ω`, then `σ` acts on
`φ` by postcomposition with `toAlgEquiv σ`. -/
theorem app_of_field [IsAlgClosure K Ω] (L : Type u) [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] [Algebra.Etale K L] (φ : L →ₐ[K] Ω) :
    σ.hom.app (Opposite.op (CommAlgCat.FiniteEtale.of K L)) φ =
      (toAlgEquiv σ).toAlgHom.comp φ := by
  haveI hfin : Module.Finite K ↥(φ.fieldRange) :=
    Module.Finite.of_surjective (φ.equivFieldRange : L →ₐ[K] ↥(φ.fieldRange)).toLinearMap
      (AlgEquiv.surjective φ.equivFieldRange)
  haveI hsep : Algebra.IsSeparable K ↥(φ.fieldRange) :=
    AlgEquiv.Algebra.isSeparable φ.equivFieldRange
  have hcomp : (IntermediateField.val φ.fieldRange).comp
      (φ.equivFieldRange : L →ₐ[K] ↥(φ.fieldRange)) = φ := by
    ext x
    simp [AlgHom.equivFieldRange_apply_coe]
  have key := app_comp (σ := σ)
    (S := CommAlgCat.FiniteEtale.of K L)
    (T := CommAlgCat.FiniteEtale.of K ↥(φ.fieldRange))
    (g := (φ.equivFieldRange : L →ₐ[K] ↥(φ.fieldRange)))
    (h := IntermediateField.val φ.fieldRange)
  rw [hcomp] at key
  have h2 : σ.hom.app (Opposite.op (CommAlgCat.FiniteEtale.of K ↥(φ.fieldRange)))
      (IntermediateField.val φ.fieldRange) =
      (toAlgEquiv σ).toAlgHom.comp (IntermediateField.val φ.fieldRange) :=
    (toAlgEquiv_comp_val (σ := σ) φ.fieldRange).symm
  rw [h2] at key
  rw [key, AlgHom.comp_assoc, hcomp]

/-! #### 6. The general case -/

/-- **The missing statement of S1748.**  Every natural automorphism `σ` of the geometric fibre
functor acts on `f : A →ₐ[K] Ω` by postcomposition with `toAlgEquiv σ`. -/
theorem app_eq_comp [IsAlgClosure K Ω] (σ : Aut (fiber (K := K) (Ω := Ω)))
    (A : C K) (f : A.unop →ₐ[K] Ω) :
    σ.hom.app A f = (toAlgEquiv σ).toAlgHom.comp f := by
  classical
  obtain ⟨ι, hι, L, hLfield, hLalg, e, hsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A.unop).mp inferInstance
  letI : Finite ι := hι
  letI : Fintype ι := Fintype.ofFinite ι
  letI : ∀ i, Field (L i) := hLfield
  letI : ∀ i, Algebra K (L i) := hLalg
  let F : (Π i, L i) →ₐ[K] Ω := f.comp e.symm.toAlgHom
  have hf : f = F.comp e.toAlgHom := by
    ext x
    simp [F]
  obtain ⟨j, G, hG⟩ := exists_comp_evalAlgHom (K := K) (Ω := Ω) L F
  haveI hFinite : Module.Finite K (L j) := (hsep j).1
  haveI hSep : Algebra.IsSeparable K (L j) := (hsep j).2
  haveI hEtale : Algebra.Etale K (L j) := etale_of_finite_separable (L j)
  let π : A.unop →ₐ[K] L j := (Pi.evalAlgHom K L j).comp e.toAlgHom
  have hfπ : f = G.comp π := by
    rw [hf, hG, AlgHom.comp_assoc]
  have key := app_comp (σ := σ) (S := A.unop)
    (T := CommAlgCat.FiniteEtale.of K (L j)) (g := π) (h := G)
  rw [← hfπ] at key
  rw [key, app_of_field (σ := σ) (L j) G, AlgHom.comp_assoc, ← hfπ]

/-- **`PostcompSurjective` holds.** -/
theorem postcompSurjective [IsAlgClosure K Ω] : PostcompSurjective (K := K) (Ω := Ω) := by
  intro σ
  refine ⟨toAlgEquiv σ, ?_⟩
  ext A f
  rw [postcomp_hom_app_apply]
  exact (app_eq_comp σ A f).symm

/-- **The comparison `Aut (fiber K Ω) ≃* (Ω ≃ₐ[K] Ω)`, unconditionally.** -/
noncomputable def autFiberEquiv [IsAlgClosure K Ω] :
    Aut (fiber (K := K) (Ω := Ω)) ≃* (Ω ≃ₐ[K] Ω) :=
  autFiberEquivOfSurjective postcompSurjective

end S1782PostcompSurjective

/-!
### Axiom audit for the new results
-/

#print axioms S1782PostcompSurjective.app_comp
#print axioms S1782PostcompSurjective.toAlgEquiv_comp_val
#print axioms S1782PostcompSurjective.exists_comp_evalAlgHom
#print axioms S1782PostcompSurjective.etale_of_finite_separable
#print axioms S1782PostcompSurjective.app_of_field
#print axioms S1782PostcompSurjective.app_eq_comp
#print axioms S1782PostcompSurjective.postcompSurjective
#print axioms S1782PostcompSurjective.autFiberEquiv
