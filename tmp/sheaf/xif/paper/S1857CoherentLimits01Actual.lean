/-
# S1857: the coherent category at the target hom universe has the same
  pullbacks and finite coproducts as at the 2-isomorphism universe

S1854 constructed two actual coherent categories on the same object type
`CoherentCover`:

* `S1854CoherentCategory11 : Category.{1,1} CoherentCover`, whose homs are the
  2-isomorphism classes `S1854CoherentQuot A B` of compatible cover maps;
* `S1854CoherentCategory01 : Category.{0,1} CoherentCover`, whose homs are the
  S1766 Type-0 small carriers `S1854SmallHom A B`.

S1856 proved, for the Category.{1,1} version, that

  HasPullbacks S1728Cover + pullback-apex coherence -> HasPullbacks CoherentCover,
  HasInitial/BinaryCoproducts S1728Cover + coproduct-apex coherence
    -> HasFiniteCoproducts CoherentCover,

using the full subcategory of `S1728Cover` on the strict image of the coherent
covers.  Those statements are stated at `S1854CoherentCategory11`; the target
fields of the paper, however, live at `Category.{0,1}`, i.e. at
`S1854CoherentCategory01`.

## What is built here

1. The hom equivalence

     S1857HomEquiv A B : (A --> B at C11)  ≃  (A --> B at C01)

   is the composite of S1854's `S1854QuotEquiv` (compatible classes ≃ S1728
   cover-map classes) with the inverse of S1809/S1766's small-carrier
   equivalence `S1854SmallHomEquiv`.  Both categories are the transport of the
   same S1728 quotient category along these hom equivalences, so the identity
   on objects is a functor in both directions:

     S1857Coherent11To01 : C11 ⥤ C01,
     S1857Coherent01To11 : C01 ⥤ C11,

   with maps given by `S1857HomEquiv` and its inverse.  Their functor laws are
   proved from the definition of the transported category structure
   (`S1857Id11_def`, `S1857Comp11_def`, `S1857Id01_def`, `S1857Comp01_def`);
   no composition or identity is fabricated.

2. Both functors are full, faithful and essentially surjective (they are the
   identity on objects), hence equivalences.  The bundled equivalences are

     S1857CoherentEquivalence    : C11 ≌ C01,
     S1857CoherentEquivalenceInv : C01 ≌ C11.

3. The S1856 limit structures are transported across the equivalence
   `S1857Coherent01To11` (from C01 to C11, the direction needed by
   `Adjunction.hasLimitsOfShape_of_equivalence` and its colimit analogue):

     S1857HasPullbacks01        : HasPullbacks S1728Cover ->
                                  S1854PullbackApexCoherent h -> HasPullbacks C01,
     S1857HasInitial01          : ... -> HasInitial C01,
     S1857HasBinaryCoproducts01 : ... -> HasBinaryCoproducts C01,
     S1857HasFiniteCoproducts01 : ... -> HasFiniteCoproducts C01.

   The hypotheses are literally S1856's: `S1854PullbackApexCoherent`,
   `S1854CoproductApexCoherent`, `S1832FirstMissingPullback`,
   `S1833FirstMissing`.  The resulting limits are the actual Mathlib limits in
   the actual Category.{0,1} structure on the coherent covers, transported by
   the equivalence of categories.

4. The exact first-missing forms at the target universe:

     S1857HasPullbacks01_of_firstMissing :
       S1856PullbackFirstMissing -> HasPullbacks C01,
     S1857HasFiniteCoproducts01_of_firstMissing :
       S1856CoproductFirstMissing -> HasFiniteCoproducts C01.

5. Compatibility with the already established forgetful functors: the composite
   C11 -> C01 -> S1809CoverCategory01 -> S1728Cover agrees with
   `S1854Forget11` on objects and homs (S1857ForgetTriangle_obj/_map).

## Honest boundary

No new axioms, no sorry, no fake category and no fake limit.  Both categories
and both functors are the actual S1854/S1809 objects; the only inputs of the
transport theorems are the S1856 hypotheses, namely S1832's bicategorical
pullback datum together with apex coherence, and S1833's finite-coproduct datum
together with apex coherence.  Nothing here proves those geometric inputs.
Only propext, Classical.choice and Quot.sound occur; see the audit block.
-/

import tmp.sheaf.xif.paper.S1856CoherentLimitsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1857CoherentLimits01Actual

open CategoryTheory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut

open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1766CanonicalModelInjectivityActual
open LeanFormal.IUT.XiFPaper.S1809SmallCarrierCategoryActual
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1833ActualCoverCoproductsActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1856CoherentLimitsActual

attribute [local instance] S1854CoherentCategory11 S1854CoherentCategory01

/-! ## 1. The hom equivalence between the two coherent categories -/

/-- The homs of the coherent category at the 2-isomorphism universe. -/
abbrev S1857Hom11 (A B : CoherentCover) : Type 1 :=
  @Quiver.Hom CoherentCover S1854CoherentCategory11.toQuiver A B

/-- The homs of the coherent category at the target (Type-0) universe. -/
abbrev S1857Hom01 (A B : CoherentCover) : Type :=
  @Quiver.Hom CoherentCover S1854CoherentCategory01.toQuiver A B

/-- **The hom equivalence between the two coherent categories.**  It sends a
2-isomorphism class of compatible cover maps to the same S1728 cover-map class,
re-read through the S1766/S1809 Type-0 small carrier.  Both categories are
transports of the same S1728 quotient category, so this is the actual
comparison of their hom families, not a choice of new maps. -/
noncomputable abbrev S1857HomEquiv (A B : CoherentCover) :
    S1857Hom11 A B ≃ S1857Hom01 A B :=
  (S1854QuotEquiv A B).trans (S1854SmallHomEquiv A B).symm

/-- The composition in `S1728Cover` used by both transported categories. -/
abbrev S1857CompClass {A B C : S1728Cover}
    (f : S1728CoverMapClass (A := A) (B := B))
    (g : S1728CoverMapClass (A := B) (B := C)) : S1728CoverMapClass (A := A) (B := C) :=
  @CategoryStruct.comp S1728Cover S1728CoverCategory11.toCategoryStruct A B C f g

/-- The identity of the coherent category at the 2-isomorphism universe. -/
abbrev S1857Id11 (A : CoherentCover) : S1857Hom11 A A :=
  @CategoryStruct.id CoherentCover S1854CoherentCategory11.toCategoryStruct A

/-- The composition of the coherent category at the 2-isomorphism universe. -/
abbrev S1857Comp11 {A B C : CoherentCover} (f : S1857Hom11 A B)
    (g : S1857Hom11 B C) : S1857Hom11 A C :=
  @CategoryStruct.comp CoherentCover S1854CoherentCategory11.toCategoryStruct A B C f g

/-- The identity of the coherent category at the target universe. -/
abbrev S1857Id01 (A : CoherentCover) : S1857Hom01 A A :=
  @CategoryStruct.id CoherentCover S1854CoherentCategory01.toCategoryStruct A

/-- The composition of the coherent category at the target universe. -/
abbrev S1857Comp01 {A B C : CoherentCover} (f : S1857Hom01 A B)
    (g : S1857Hom01 B C) : S1857Hom01 A C :=
  @CategoryStruct.comp CoherentCover S1854CoherentCategory01.toCategoryStruct A B C f g

/-- Definition of the identity at the 2-isomorphism universe. -/
theorem S1857Id11_def (A : CoherentCover) :
    S1857Id11 A = (S1854QuotEquiv A A).symm (𝟙 (A.cover)) := rfl

/-- Definition of the identity at the target universe. -/
theorem S1857Id01_def (A : CoherentCover) :
    S1857Id01 A = (S1854SmallHomEquiv A A).symm (𝟙 (A.cover)) := rfl

/-- Definition of the composition at the 2-isomorphism universe. -/
theorem S1857Comp11_def {A B C : CoherentCover} (f : S1857Hom11 A B)
    (g : S1857Hom11 B C) :
    S1857Comp11 f g = (S1854QuotEquiv A C).symm
      (S1857CompClass ((S1854QuotEquiv A B) f) ((S1854QuotEquiv B C) g)) := rfl

/-- Definition of the composition at the target universe. -/
theorem S1857Comp01_def {A B C : CoherentCover} (f : S1857Hom01 A B)
    (g : S1857Hom01 B C) :
    S1857Comp01 f g = (S1854SmallHomEquiv A C).symm
      (S1857CompClass ((S1854SmallHomEquiv A B) f) ((S1854SmallHomEquiv B C) g)) := rfl

/-! ## 2. The identity-on-objects functors between the two categories -/

/-- **The functor from the 2-isomorphism category to the target category.**  It
is the identity on coherent covers and `S1857HomEquiv` on homs. -/
noncomputable def S1857Coherent11To01 :
    @CategoryTheory.Functor CoherentCover S1854CoherentCategory11
      CoherentCover S1854CoherentCategory01 where
  obj A := A
  map {A B} f := S1857HomEquiv A B f
  map_id A := by
    change S1857HomEquiv A A (S1857Id11 A) = S1857Id01 A
    rw [S1857Id11_def, S1857Id01_def]
    change (S1854SmallHomEquiv A A).symm
        ((S1854QuotEquiv A A) ((S1854QuotEquiv A A).symm (𝟙 (A.cover))))
      = (S1854SmallHomEquiv A A).symm (𝟙 (A.cover))
    rw [Equiv.apply_symm_apply]
  map_comp {A B C} f g := by
    change S1857HomEquiv A C (S1857Comp11 f g)
      = S1857Comp01 (S1857HomEquiv A B f) (S1857HomEquiv B C g)
    rw [S1857Comp11_def, S1857Comp01_def]
    change (S1854SmallHomEquiv A C).symm
        ((S1854QuotEquiv A C) ((S1854QuotEquiv A C).symm
          (S1857CompClass ((S1854QuotEquiv A B) f) ((S1854QuotEquiv B C) g))))
      = (S1854SmallHomEquiv A C).symm
          (S1857CompClass
            ((S1854SmallHomEquiv A B) ((S1854SmallHomEquiv A B).symm
              ((S1854QuotEquiv A B) f)))
            ((S1854SmallHomEquiv B C) ((S1854SmallHomEquiv B C).symm
              ((S1854QuotEquiv B C) g))))
    simp only [Equiv.apply_symm_apply]

/-- **The functor from the target category to the 2-isomorphism category.**
The inverse on homs of `S1857Coherent11To01`; still the identity on objects. -/
noncomputable def S1857Coherent01To11 :
    @CategoryTheory.Functor CoherentCover S1854CoherentCategory01
      CoherentCover S1854CoherentCategory11 where
  obj A := A
  map {A B} f := (S1857HomEquiv A B).symm f
  map_id A := by
    change (S1857HomEquiv A A).symm (S1857Id01 A) = S1857Id11 A
    rw [S1857Id01_def, S1857Id11_def]
    change (S1854QuotEquiv A A).symm
        ((S1854SmallHomEquiv A A) ((S1854SmallHomEquiv A A).symm (𝟙 (A.cover))))
      = (S1854QuotEquiv A A).symm (𝟙 (A.cover))
    rw [Equiv.apply_symm_apply]
  map_comp {A B C} f g := by
    change (S1857HomEquiv A C).symm (S1857Comp01 f g)
      = S1857Comp11 ((S1857HomEquiv A B).symm f) ((S1857HomEquiv B C).symm g)
    rw [S1857Comp01_def, S1857Comp11_def]
    change (S1854QuotEquiv A C).symm
        ((S1854SmallHomEquiv A C) ((S1854SmallHomEquiv A C).symm
          (S1857CompClass ((S1854SmallHomEquiv A B) f) ((S1854SmallHomEquiv B C) g))))
      = (S1854QuotEquiv A C).symm
          (S1857CompClass
            ((S1854QuotEquiv A B) ((S1854QuotEquiv A B).symm
              ((S1854SmallHomEquiv A B) f)))
            ((S1854QuotEquiv B C) ((S1854QuotEquiv B C).symm
              ((S1854SmallHomEquiv B C) g))))
    simp only [Equiv.apply_symm_apply]

/-! ## 3. Fullness, faithfulness, essential surjectivity, and the equivalence -/

instance S1857Coherent11To01_full : S1857Coherent11To01.Full where
  map_surjective {A B} g :=
    ⟨(S1857HomEquiv A B).symm g, by
      change S1857HomEquiv A B ((S1857HomEquiv A B).symm g) = g
      exact Equiv.apply_symm_apply _ _⟩

instance S1857Coherent11To01_faithful : S1857Coherent11To01.Faithful where
  map_injective {A B} f g h := by
    exact (S1857HomEquiv A B).injective h

instance S1857Coherent11To01_essSurj : S1857Coherent11To01.EssSurj where
  mem_essImage A := ⟨A, ⟨@Iso.refl CoherentCover S1854CoherentCategory01 A⟩⟩

instance S1857Coherent11To01_isEquivalence : S1857Coherent11To01.IsEquivalence where

instance S1857Coherent01To11_full : S1857Coherent01To11.Full where
  map_surjective {A B} g :=
    ⟨S1857HomEquiv A B g, by
      change (S1857HomEquiv A B).symm (S1857HomEquiv A B g) = g
      exact Equiv.symm_apply_apply _ _⟩

instance S1857Coherent01To11_faithful : S1857Coherent01To11.Faithful where
  map_injective {A B} f g h := by
    exact (S1857HomEquiv A B).symm.injective h

instance S1857Coherent01To11_essSurj : S1857Coherent01To11.EssSurj where
  mem_essImage A := ⟨A, ⟨@Iso.refl CoherentCover S1854CoherentCategory11 A⟩⟩

instance S1857Coherent01To11_isEquivalence : S1857Coherent01To11.IsEquivalence where

/-- **The bundled equivalence between the two actual coherent categories.** -/
noncomputable def S1857CoherentEquivalence :
    @CategoryTheory.Equivalence CoherentCover CoherentCover
      S1854CoherentCategory11 S1854CoherentCategory01 :=
  S1857Coherent11To01.asEquivalence

/-- **The bundled equivalence in the other direction.** -/
noncomputable def S1857CoherentEquivalenceInv :
    @CategoryTheory.Equivalence CoherentCover CoherentCover
      S1854CoherentCategory01 S1854CoherentCategory11 :=
  S1857Coherent01To11.asEquivalence

/-! ## 4. Transport of the S1856 limit structures to the target universe -/

/-- **The coherent Category.{0,1} has pullbacks**, given the same two inputs as
S1856's `S1856HasPullbacks`: S1728 pullbacks and pullback-apex coherence.
This is the actual `HasPullbacks` at `S1854CoherentCategory01`, obtained by
transporting S1856's `HasLimitsOfShape WalkingCospan` across the equivalence
`S1857Coherent01To11`. -/
theorem S1857HasPullbacks01 (h : Limits.HasPullbacks S1728Cover)
    (hA : S1854PullbackApexCoherent h) :
    @Limits.HasPullbacks CoherentCover S1854CoherentCategory01 :=
  @CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory11 CoherentCover S1854CoherentCategory01
    WalkingCospan _ S1857Coherent01To11 S1857Coherent01To11_isEquivalence
    (S1856HasPullbacks h hA)

/-- **The coherent Category.{0,1} has an initial object**, from S1856's
`S1856HasInitial` and the coproduct-apex coherence. -/
theorem S1857HasInitial01 (h0 : Limits.HasInitial S1728Cover)
    (h2 : Limits.HasBinaryCoproducts S1728Cover)
    (hA : S1854CoproductApexCoherent h0 h2) :
    @Limits.HasInitial CoherentCover S1854CoherentCategory01 :=
  @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory01 CoherentCover S1854CoherentCategory11
    (Discrete.{0} PEmpty) _ S1857Coherent01To11 S1857Coherent01To11_isEquivalence
    (S1856HasInitial h0 h2 hA)

/-- **The coherent Category.{0,1} has binary coproducts**, from S1856's
`S1856HasBinaryCoproducts` and the coproduct-apex coherence. -/
theorem S1857HasBinaryCoproducts01 (h0 : Limits.HasInitial S1728Cover)
    (h2 : Limits.HasBinaryCoproducts S1728Cover)
    (hA : S1854CoproductApexCoherent h0 h2) :
    @Limits.HasBinaryCoproducts CoherentCover S1854CoherentCategory01 :=
  @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory01 CoherentCover S1854CoherentCategory11
    (Discrete WalkingPair) _ S1857Coherent01To11 S1857Coherent01To11_isEquivalence
    (S1856HasBinaryCoproducts h0 h2 hA)

/-- **The coherent Category.{0,1} has finite coproducts**, from S1856's
`S1856HasFiniteCoproducts` and the coproduct-apex coherence.  Each finite
coproduct shape `Discrete (Fin n)` is transported separately, so this uses the
actual `HasFiniteCoproducts.out` fields of S1856's statement. -/
theorem S1857HasFiniteCoproducts01 (h0 : Limits.HasInitial S1728Cover)
    (h2 : Limits.HasBinaryCoproducts S1728Cover)
    (hA : S1854CoproductApexCoherent h0 h2) :
    @Limits.HasFiniteCoproducts CoherentCover S1854CoherentCategory01 := by
  refine ⟨fun n => ?_⟩
  exact @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory01 CoherentCover S1854CoherentCategory11
    (Discrete (Fin n)) _ S1857Coherent01To11 S1857Coherent01To11_isEquivalence
    ((S1856HasFiniteCoproducts h0 h2 hA).out n)

/-! ## 5. The exact first-missing forms at the target universe -/

/-- **The pullback first missing suffices for `HasPullbacks` at
`S1854CoherentCategory01`.**  The hypotheses are S1856's own
`S1856PullbackFirstMissing`, i.e. S1832's bicategorical pullback datum together
with pullback-apex coherence for the pullback structure it induces. -/
theorem S1857HasPullbacks01_of_firstMissing :
    S1856PullbackFirstMissing →
      @Limits.HasPullbacks CoherentCover S1854CoherentCategory01 := by
  rintro ⟨h, hA⟩
  exact S1857HasPullbacks01 (S1832HasPullbacks_of_squares h) hA

/-- **The coproduct first missing suffices for finite coproducts at
`S1854CoherentCategory01`.**  The hypotheses are S1856's own
`S1856CoproductFirstMissing`. -/
theorem S1857HasFiniteCoproducts01_of_firstMissing :
    S1856CoproductFirstMissing →
      @Limits.HasFiniteCoproducts CoherentCover S1854CoherentCategory01 := by
  rintro ⟨_, h0, h2, hA⟩
  exact S1857HasFiniteCoproducts01 h0 h2 hA

/-- The target-universe form of the S1856 transport, summarized: the same
S1856 hypotheses give pullbacks and finite coproducts at
`S1854CoherentCategory01`. -/
theorem S1857Limits01Summary :
    (∀ (h : Limits.HasPullbacks S1728Cover), S1854PullbackApexCoherent h →
      @Limits.HasPullbacks CoherentCover S1854CoherentCategory01) ∧
    (∀ (h0 : Limits.HasInitial S1728Cover)
      (h2 : Limits.HasBinaryCoproducts S1728Cover),
      S1854CoproductApexCoherent h0 h2 →
        @Limits.HasFiniteCoproducts CoherentCover S1854CoherentCategory01) :=
  ⟨S1857HasPullbacks01, S1857HasFiniteCoproducts01⟩

/-! ## 6. Compatibility with the forgetful functors

The equivalence is not an abstract transport of a category structure: the two
coherent categories are both built over the S1728 cover category, and the
composite C11 -> C01 -> S1809CoverCategory01 -> S1728Cover is exactly the
already established forgetful functor `S1854Forget11`.  The next two lemmas
record this compatibility on objects and homs. -/

/-- The forgetful triangle is the identity on objects.  The functor projections
are applied with their category-instance arguments explicit, because the target
`S1809CoverCategory01` is not a global instance. -/
theorem S1857ForgetTriangle_obj (A : CoherentCover) :
    @CategoryTheory.Functor.obj S1728Cover S1809CoverCategory01 S1728Cover
      S1728CoverCategory11 S1809ComparisonFunctor
      (@CategoryTheory.Functor.obj CoherentCover S1854CoherentCategory01 S1728Cover
        S1809CoverCategory01 S1854Forget01
        (@CategoryTheory.Functor.obj CoherentCover S1854CoherentCategory11
          CoherentCover S1854CoherentCategory01 S1857Coherent11To01 A))
      = @CategoryTheory.Functor.obj CoherentCover S1854CoherentCategory11
          S1728Cover S1728CoverCategory11 S1854Forget11 A := rfl

/-- The forgetful triangle is the identity on homs, i.e. the hom equivalence
`S1857HomEquiv` is exactly the S1854 comparison through the S1809/S1766 small
carrier.  Again the functor projections are applied with explicit category
instances. -/
theorem S1857ForgetTriangle_map {A B : CoherentCover} (f : S1857Hom11 A B) :
    @CategoryTheory.Functor.map S1728Cover S1809CoverCategory01 S1728Cover
      S1728CoverCategory11 S1809ComparisonFunctor A.cover B.cover
      (@CategoryTheory.Functor.map CoherentCover S1854CoherentCategory01 S1728Cover
        S1809CoverCategory01 S1854Forget01 A B
        (@CategoryTheory.Functor.map CoherentCover S1854CoherentCategory11
          CoherentCover S1854CoherentCategory01 S1857Coherent11To01 A B f))
      = @CategoryTheory.Functor.map CoherentCover S1854CoherentCategory11
          S1728Cover S1728CoverCategory11 S1854Forget11 A B f := by
  change (S1766QuotSmallEquiv A.cover B.cover).symm
      ((S1766QuotSmallEquiv A.cover B.cover) (S1854QuotEquiv A B f))
    = S1854QuotEquiv A B f
  exact Equiv.symm_apply_apply _ _

/-! ## 7. Checks and axiom audit -/

#check @S1857Hom11
#check @S1857Hom01
#check S1857HomEquiv
#check S1857Id11_def
#check S1857Id01_def
#check S1857Comp11_def
#check S1857Comp01_def
#check @S1857Coherent11To01
#check @S1857Coherent01To11
#check S1857Coherent11To01_full
#check S1857Coherent11To01_faithful
#check S1857Coherent11To01_essSurj
#check S1857Coherent11To01_isEquivalence
#check S1857Coherent01To11_full
#check S1857Coherent01To11_faithful
#check S1857Coherent01To11_essSurj
#check S1857Coherent01To11_isEquivalence
#check @S1857CoherentEquivalence
#check @S1857CoherentEquivalenceInv
#check @S1857HasPullbacks01
#check @S1857HasInitial01
#check @S1857HasBinaryCoproducts01
#check @S1857HasFiniteCoproducts01
#check S1857HasPullbacks01_of_firstMissing
#check S1857HasFiniteCoproducts01_of_firstMissing
#check S1857Limits01Summary
#check S1857ForgetTriangle_obj
#check S1857ForgetTriangle_map

-- The transported statements are literally at the target universe
-- `Category.{0,1}`, not at the 2-isomorphism universe.
example (h : Limits.HasPullbacks S1728Cover) (hA : S1854PullbackApexCoherent h) :
    @Limits.HasPullbacks CoherentCover S1854CoherentCategory01 :=
  S1857HasPullbacks01 h hA

example (h0 : Limits.HasInitial S1728Cover)
    (h2 : Limits.HasBinaryCoproducts S1728Cover)
    (hA : S1854CoproductApexCoherent h0 h2) :
    @Limits.HasFiniteCoproducts CoherentCover S1854CoherentCategory01 :=
  S1857HasFiniteCoproducts01 h0 h2 hA

#print axioms S1857HomEquiv
#print axioms S1857Coherent11To01
#print axioms S1857Coherent01To11
#print axioms S1857Coherent11To01_full
#print axioms S1857Coherent11To01_faithful
#print axioms S1857Coherent11To01_essSurj
#print axioms S1857Coherent11To01_isEquivalence
#print axioms S1857Coherent01To11_full
#print axioms S1857Coherent01To11_faithful
#print axioms S1857Coherent01To11_essSurj
#print axioms S1857Coherent01To11_isEquivalence
#print axioms S1857CoherentEquivalence
#print axioms S1857CoherentEquivalenceInv
#print axioms S1857HasPullbacks01
#print axioms S1857HasInitial01
#print axioms S1857HasBinaryCoproducts01
#print axioms S1857HasFiniteCoproducts01
#print axioms S1857HasPullbacks01_of_firstMissing
#print axioms S1857HasFiniteCoproducts01_of_firstMissing
#print axioms S1857Limits01Summary
#print axioms S1857ForgetTriangle_map

end LeanFormal.IUT.XiFPaper.S1857CoherentLimits01Actual
