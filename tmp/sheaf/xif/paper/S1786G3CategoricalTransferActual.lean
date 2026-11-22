import tmp.sheaf.xif.paper.S1747FiniteEtaleMonoSplitActual

/-!
# S1786: the (G3) field of `PreGaloisCategory` for `(CommAlgCat.FiniteEtale K)^op`

S1747 reduced the categorical axiom

  `PreGaloisCategory.monoInducesIsoOnDirectSummand`

for `(CommAlgCat.FiniteEtale K)^op` to two algebraic statements on finite etale
`K`-algebras:

* `S1747.EpiSurjective K`: an epimorphism of finite etale `K`-algebras is surjective;
* `S1747.SurjectiveSplit K`: a surjective map of finite etale `K`-algebras is, up to an
  algebra isomorphism `B ≃ₐ[K] A × C`, the first projection.

This file performs the remaining **categorical transfer**: it proves, from those two
statements (or from the combined algebraic splitting statement `FiniteEtaleSplit K`),
that every monomorphism `i : X ⟶ Y` in `(CommAlgCat.FiniteEtale K)^op` is a coproduct
injection.  This is exactly the `monoInducesIsoOnDirectSummand` field of
`PreGaloisCategory`, with the same quantifiers.

## How the transfer is done

1. A monomorphism `i : X ⟶ Y` in the opposite category is an epimorphism
   `φ = i.unop : Y.unop ⟶ X.unop` of finite etale `K`-algebras.  The hypothesis of
   `EpiSurjective` is read off from `Mono.right_cancellation`.
2. `SurjectiveSplit` then gives `C` and `e : Y.unop ≃ₐ[K] X.unop × C` with
   `fst.comp e.toAlgHom = φ`.
3. In `CommAlgCat.FiniteEtale K` the binary fan `BinaryFan.mk i.unop ψD` with point
   `Y.unop` is a limit, where `ψD` is the morphism of finite etale `K`-algebras whose
   underlying algebra map is `snd.comp e.toAlgHom`.  The lift of a fan `(a, b)` is the
   algebra map `e.symm ∘ (a, b) : T ⟶ Y.unop`, and uniqueness is the universal property
   of the product `X.unop × C` read through `e`.
4. Applying `BinaryFan.IsLimit.op` turns this limit fan into the colimit cofan
   `BinaryCofan.mk i u` in the opposite category, with `Z = op (FiniteEtale.of K C)`
   and `u = (snd ∘ e).op`.

## Implementation note (the `.hom` transparency issue of S1747)

The category `(CommAlgCat.FiniteEtale K)^op` is an `ObjectProperty.FullSubcategory`, whose
morphisms are `InducedCategory.Hom` wrappers around morphisms of `CommAlgCat K`.  Rather
than unfolding these wrappers by hand, the proof uses the `ConcreteCategory` structure on
both the full subcategory and `CommAlgCat K`
(`ObjectProperty.FullSubcategory.concreteCategory`): `ConcreteCategory.hom` and
`ConcreteCategory.ofHom` move between morphisms and `AlgHom`s, and
`ConcreteCategory.ext_apply` reduces equalities of morphisms to pointwise equalities.
The definitional equalities `ConcreteCategory.hom (ofHom f) = f` and
`ConcreteCategory.hom i.unop = i.unop.hom.hom` are both `rfl` in this setup.  No
`.hom`-unfolding `simp` lemma is needed.

## Result

There is no `sorry`, no new axiom and no weakened statement.  The main declarations are

* `S1786.monoInducesIsoOnDirectSummand_of_split`, from `FiniteEtaleSplit K`;
* `S1786.monoInducesIsoOnDirectSummand_of_epiSurjective_of_surjectiveSplit`, from
  `S1747.EpiSurjective K` and `S1747.SurjectiveSplit K`;
* `S1786.monoInducesIsoOnDirectSummand_field`, the same statement in the literal form of
  the `PreGaloisCategory` field;
* `S1786.preGaloisCategory_of_fields`, which puts the transferred field into an actual
  `PreGaloisCategory` instance once the other fields are supplied.

## Verification (session S1786, 2026-11-01)

* Compile command (from `D:\lean`):
  `lake env lean -j1 -R 'D:\lean' -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1786G3CategoricalTransferActual.olean tmp/sheaf/xif/paper/S1786G3CategoricalTransferActual.lean`
  -> EXIT=0, no warnings, no errors.
* Axiom audit: every `#print axioms` below prints exactly
  `[propext, Classical.choice, Quot.sound]`; in particular no `sorryAx`.
* Integration check (external probe, not part of this file): a file importing this module
  and S1767 checks that `S1786.MonoInducesIsoOnDirectSummandField K` is definitionally
  `S1767FiniteEtaleGalois.MonoInducesIsoOnDirectSummandField K`, and builds the actual
  `PreGaloisCategory ((CommAlgCat.FiniteEtale K)^op)` instance with this (G3) field and
  the other fields supplied by S1745/S1767; it compiles with EXIT=0.

## References

* S1747: `tmp/sheaf/xif/paper/S1747FiniteEtaleMonoSplitActual.lean`
* Lenstra, *Galois theory for schemes*, Definition 3.1 (G3).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace S1786

/-- The opposite of the category of finite etale `K`-algebras. -/
abbrev FiniteEtaleAlg (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ

/-- The exact `monoInducesIsoOnDirectSummand` field of `PreGaloisCategory` for
`(CommAlgCat.FiniteEtale K)^op`: every monomorphism induces an isomorphism on a direct
summand, i.e. it is the first injection of a binary coproduct.

The class takes `[Mono i]` as an instance argument; here it is an explicit argument,
which is the same proposition with the same quantifiers. -/
def MonoInducesIsoOnDirectSummandField (K : Type) [Field K] : Prop :=
  ∀ {X Y : FiniteEtaleAlg K} (i : X ⟶ Y), Mono i →
    ∃ (Z : FiniteEtaleAlg K) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u))

/-- The combined algebraic splitting statement for finite etale `K`-algebras: an
epimorphism `φ : B →ₐ[K] A` is, up to an algebra isomorphism `B ≃ₐ[K] A × C`, the first
projection.

This is exactly the conclusion of
`S1747.finiteEtaleSplit_of_epiSurjective_of_surjectiveSplit`. -/
def FiniteEtaleSplit (K : Type) [Field K] : Prop :=
  ∀ (A B : Type) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    [CommRing B] [Algebra K B] [Module.Finite K B] [Algebra.Etale K B]
    (φ : B →ₐ[K] A),
    (∀ (T : Type) [CommRing T] [Algebra K T] [Module.Finite K T] [Algebra.Etale K T]
      (g h : A →ₐ[K] T), g.comp φ = h.comp φ → g = h) →
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra K C) (_ : Module.Finite K C)
      (_ : Algebra.Etale K C) (e : B ≃ₐ[K] A × C),
      (AlgHom.fst (R := K) (A := A) (B := C)).comp e.toAlgHom = φ

/-- `FiniteEtaleSplit K` follows from S1747's two algebraic statements. -/
theorem finiteEtaleSplit_of_epiSurjective_of_surjectiveSplit {K : Type} [Field K]
    (hEpi : S1747.EpiSurjective K) (hSplit : S1747.SurjectiveSplit K) :
    FiniteEtaleSplit K :=
  S1747.finiteEtaleSplit_of_epiSurjective_of_surjectiveSplit hEpi hSplit

/-- **The categorical transfer.**  From the algebraic splitting of epimorphisms of finite
etale `K`-algebras, every monomorphism in `(CommAlgCat.FiniteEtale K)^op` is a coproduct
injection.  This is precisely the (G3) field of `PreGaloisCategory`. -/
theorem monoInducesIsoOnDirectSummand_of_split {K : Type} [Field K]
    (hsplit : FiniteEtaleSplit K) : MonoInducesIsoOnDirectSummandField K := by
  intro X Y i hmono
  -- Work in the opposite direction: `i` becomes an epimorphism of finite etale algebras.
  let A := X.unop
  let B := Y.unop
  let φ : B →ₐ[K] A := ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) i.unop
  have hφ : ∀ (T : Type) [CommRing T] [Algebra K T] [Module.Finite K T] [Algebra.Etale K T]
      (g h : A →ₐ[K] T), g.comp φ = h.comp φ → g = h := by
    intro T _ _ _ _ g h hgh
    let W : FiniteEtaleAlg K := op (CommAlgCat.FiniteEtale.of K T)
    let f : W ⟶ X := (ConcreteCategory.ofHom (C := CommAlgCat.FiniteEtale.{0} K) g).op
    let f' : W ⟶ X := (ConcreteCategory.ofHom (C := CommAlgCat.FiniteEtale.{0} K) h).op
    have hcomp : f ≫ i = f' ≫ i := by
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      ext x
      exact AlgHom.congr_fun hgh x
    have hff : f = f' := Mono.right_cancellation (f := i) f f' hcomp
    have hres := congrArg (fun k : W ⟶ X =>
      ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) k.unop) hff
    simpa [f, f'] using hres
  -- The algebraic splitting.
  obtain ⟨C, hCring, hCalg, hCfin, hCetale, e, he⟩ := hsplit A B φ hφ
  letI : CommRing C := hCring
  letI : Algebra K C := hCalg
  letI : Module.Finite K C := hCfin
  letI : Algebra.Etale K C := hCetale
  -- The complement `Z` and the second projection `u`.
  let Z : FiniteEtaleAlg K := op (CommAlgCat.FiniteEtale.of K C)
  let ψ : B →ₐ[K] C := (AlgHom.snd (R := K) (A := A) (B := C)).comp e.toAlgHom
  let ψD : Y.unop ⟶ Z.unop := ConcreteCategory.ofHom (C := CommAlgCat.FiniteEtale.{0} K) ψ
  let u : Z ⟶ Y := ψD.op
  -- The corresponding binary fan in `CommAlgCat.FiniteEtale K`.
  let s : BinaryFan X.unop Z.unop := BinaryFan.mk i.unop ψD
  have hlim : IsLimit s := by
    let lift : ∀ t : BinaryFan X.unop Z.unop, t.pt ⟶ Y.unop := fun t =>
      let prodMap : t.pt →ₐ[K] A × C :=
        (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.fst).prod
          (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.snd)
      ConcreteCategory.ofHom (C := CommAlgCat.FiniteEtale.{0} K) (e.symm.toAlgHom.comp prodMap)
    have hfac1 : ∀ t : BinaryFan X.unop Z.unop, lift t ≫ i.unop = t.fst := by
      intro t
      apply ConcreteCategory.ext_apply
      intro x
      rw [ConcreteCategory.comp_apply]
      have hlift : lift t x = e.symm ((ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K)
          t.fst).prod (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.snd) x) := rfl
      rw [hlift]
      change φ (e.symm ((ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.fst).prod
          (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.snd) x)) = t.fst x
      have hpt : ((e (e.symm ((ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.fst).prod
          (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.snd) x))).1) =
          φ (e.symm ((ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.fst).prod
          (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.snd) x)) :=
        AlgHom.congr_fun he _
      rw [← hpt, AlgEquiv.apply_symm_apply]
      rfl
    have hfac2 : ∀ t : BinaryFan X.unop Z.unop, lift t ≫ ψD = t.snd := by
      intro t
      apply ConcreteCategory.ext_apply
      intro x
      rw [ConcreteCategory.comp_apply]
      have hlift : lift t x = e.symm ((ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K)
          t.fst).prod (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.snd) x) := rfl
      rw [hlift]
      change ψ (e.symm ((ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.fst).prod
          (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.snd) x)) = t.snd x
      have hpt : (e (e.symm ((ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.fst).prod
          (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.snd) x))).2 =
          ψ (e.symm ((ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.fst).prod
          (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.snd) x)) := rfl
      rw [← hpt, AlgEquiv.apply_symm_apply]
      rfl
    have huniq : ∀ (t : BinaryFan X.unop Z.unop) (m : t.pt ⟶ Y.unop),
        m ≫ i.unop = t.fst → m ≫ ψD = t.snd → m = lift t := by
      intro t m hm1 hm2
      apply ConcreteCategory.ext_apply
      intro x
      have h1 : φ (m x) = t.fst x := by
        have h := ConcreteCategory.congr_hom hm1 x
        rw [ConcreteCategory.comp_apply] at h
        exact h
      have h2 : (e (m x)).2 = t.snd x := by
        have h := ConcreteCategory.congr_hom hm2 x
        rw [ConcreteCategory.comp_apply] at h
        exact h
      have h1' : (e (m x)).1 = t.fst x := by
        have h := AlgHom.congr_fun he (m x)
        exact h.trans h1
      have hprod : e (m x) = (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.fst).prod
          (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.snd) x := by
        ext
        · rw [h1']; rfl
        · rw [h2]; rfl
      calc m x = e.symm (e (m x)) := by simp
        _ = e.symm ((ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.fst).prod
              (ConcreteCategory.hom (C := CommAlgCat.FiniteEtale.{0} K) t.snd) x) := by rw [hprod]
        _ = lift t x := rfl
    exact BinaryFan.isLimitMk lift hfac1 hfac2 huniq
  -- The limit fan becomes a colimit cofan in the opposite category.
  refine ⟨Z, u, ?_⟩
  refine ⟨?_⟩
  have h := BinaryFan.IsLimit.op hlim
  simpa [s, u, ψD] using h

/-- The (G3) field from S1747's two algebraic statements. -/
theorem monoInducesIsoOnDirectSummand_of_epiSurjective_of_surjectiveSplit {K : Type} [Field K]
    (hEpi : S1747.EpiSurjective K) (hSplit : S1747.SurjectiveSplit K) :
    MonoInducesIsoOnDirectSummandField K :=
  monoInducesIsoOnDirectSummand_of_split
    (finiteEtaleSplit_of_epiSurjective_of_surjectiveSplit hEpi hSplit)

/-- The (G3) field in the literal shape of the `PreGaloisCategory` field (with `Mono i`
as an instance argument rather than as an explicit argument). -/
theorem monoInducesIsoOnDirectSummand_field {K : Type} [Field K]
    (hEpi : S1747.EpiSurjective K) (hSplit : S1747.SurjectiveSplit K) :
    ∀ {X Y : FiniteEtaleAlg K} (i : X ⟶ Y) [Mono i],
      ∃ (Z : FiniteEtaleAlg K) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)) :=
  fun {_ _} i hmono =>
    monoInducesIsoOnDirectSummand_of_epiSurjective_of_surjectiveSplit hEpi hSplit i hmono

/-- A `PreGaloisCategory` instance for `(CommAlgCat.FiniteEtale K)^op` in which the
`monoInducesIsoOnDirectSummand` field is the transferred theorem above, not a hypothesis.
The other four fields are left as explicit hypotheses (they are supplied by S1745 for
terminals/pullbacks/finite coproducts and by the quotient theory for finite groups). -/
theorem preGaloisCategory_of_fields {K : Type} [Field K]
    (hTerm : HasTerminal (FiniteEtaleAlg K))
    (hPull : HasPullbacks (FiniteEtaleAlg K))
    (hCoprod : HasFiniteCoproducts (FiniteEtaleAlg K))
    (hQuot : ∀ (G : Type) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K))
    (hEpi : S1747.EpiSurjective K) (hSplit : S1747.SurjectiveSplit K) :
    PreGaloisCategory (FiniteEtaleAlg K) where
  hasTerminal := hTerm
  hasPullbacks := hPull
  hasFiniteCoproducts := hCoprod
  hasQuotientsByFiniteGroups := hQuot
  monoInducesIsoOnDirectSummand := fun {_ _} i hmono =>
    monoInducesIsoOnDirectSummand_of_epiSurjective_of_surjectiveSplit hEpi hSplit i hmono

end S1786

/-! ### Axiom audit -/

#print axioms S1786.finiteEtaleSplit_of_epiSurjective_of_surjectiveSplit
#print axioms S1786.monoInducesIsoOnDirectSummand_of_split
#print axioms S1786.monoInducesIsoOnDirectSummand_of_epiSurjective_of_surjectiveSplit
#print axioms S1786.monoInducesIsoOnDirectSummand_field
#print axioms S1786.preGaloisCategory_of_fields