/-
# S1836: the pseudopullback stack of two actual finite-etale cover maps

## Context and target

S1832 proved that the categorical (limit) half of the pullback obligation is free:
a bicategorical two-pullback datum for a cospan of actual finite-etale cover maps
f : A -> C, g : B -> C yields a genuine limit in the 2-isomorphism quotient
S1728ActualCategory11, and conversely.  It also isolated the remaining geometric
input as the construction of the pseudopullback (iso-comma) stack of

  A.source -> C.source <- B.source

with its descent condition IsStack, together with a structure map to X.stack
which is representably finite etale.

This file attacks that statement with the actual S1726 objects.

## What is constructed unconditionally

1.  The fibre-level iso-comma S1836IsoComma L R: the full subcategory of
    Mathlib's comma category Comma L R on objects whose structure morphism is
    an isomorphism.  It has the two projections S1836IsoCommaFst and
    S1836IsoCommaSnd, the canonical 2-commuting natural isomorphism
    S1836IsoCommaNatIso : fst ; L ~ snd ; R, and the joint-faithfulness of the
    two projections (S1836IsoComma_hom_ext).  Thus the fibre of the would-be
    pseudopullback is available for every test object, without any choice.

2.  For cospans whose second (resp. first) leg is the actual identity cover map
    S1641CoverMapId, the pseudopullback stack is constructed completely:
    its apex cover is the other cover (A resp. B), its source stack is the
    actual EtaleStackOverField of that cover (so IsStack is the actual
    EtaleStackOverField.isStack field), its structure map to X.stack is the
    finite-etale cover map of that cover, and its fibres are proved equivalent
    to the iso-comma categories, compatibly with both projections
    (S1836IsoCommaRightIdEquiv, S1836IsoCommaLeftIdEquiv).  These are honest
    full constructions of the requested datum, not placeholders.

3.  A conditional packaging: a S1836PseudopullbackStackDatum f g bundles an
    actual two-pullback cover P (S1832) together with a fibre realization of
    the iso-comma categories through the two projections.  From it we extract
    the actual stack, its IsStack proof, its representably finite-etale
    structure map, and its iso-comma fibres.  The datum implies
    S1832FirstMissingPullback, hence HasPullbacks S1728ActualCategory11, the
    finite-limit field and (with the other three inputs) the actual
    PreGaloisCategory.

## The exact first missing statement

The general existence statement is

  S1836FirstMissingPseudopullbackStack : Prop
    forall A B C f g, Nonempty (S1836PseudopullbackStackDatum f g).

It is equivalent to its realization form S1836FirstMissingStackRealization
(S1836FirstMissing_iff_realization): for every cospan there is a two-pullback
cover P whose source stack realizes the iso-comma fibres through the two
projections.  It implies S1832FirstMissingPullback
(S1836FirstMissing_to_S1832), so any inhabitant would close the open pullback
obligation; no such construction is present in the tree, and this file does not
assert it.

The missing mathematical inputs, in the order in which they are needed, are:

* a category-valued pseudofunctor on the whole etale site whose value at a test
  scheme U is S1836IsoComma (f.app U) (g.app U), with the coherence isos for
  restriction; the fibre categories and their projections are constructed here,
  but the pseudofunctor comparison isomorphisms and their coherence are not;
* the descent theorem IsStack for that pseudofunctor (effective descent for
  the iso-comma of three stacks), which is not an instance of Mathlib's
  Pseudofunctor.IsStack API nor of S1761's descending-data smallness;
* the identification of the resulting stack with the two-pullback cover of
  S1832, i.e. the compatibility of the fibre equivalences with the universal
  property and with the finite-etale structure map.  Note that a cover already
  bundles its representably finite-etale structure map, so once the stack is
  the source of a cover this part is definitional; the genuinely geometric part
  is that the pseudopullback is again a finite-etale cover of X (projections
  finite etale and stability under composition), which is exactly the geometric
  input recorded by S1832 and is not present in the tree.

## Honest boundary

No sorry, no new axiom, no Shrink, ULift or PUnit, and no fake stack.
The identity-leg data are built from the actual cover maps and the actual
pseudofunctor bicategory; the general datum is a named Prop, not an asserted
inhabitant.  The only axioms used are propext, Classical.choice and
Quot.sound; see the #print axioms block at the end.
-/

import tmp.sheaf.xif.paper.S1832ActualCoverPullbacksActual
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual

universe u v w

/-! ## 1. The fibre-level iso-comma -/

/-- The iso-comma category of two functors: the full subcategory of the comma
category on the objects whose structure morphism is an isomorphism.  This is the
fibre of the pseudopullback at a test object. -/
abbrev S1836IsoComma {A : Type u} {B : Type v} {C : Type w}
    [Category A] [Category B] [Category C]
    (L : A ⥤ C) (R : B ⥤ C) : Type (max u v w) :=
  ObjectProperty.FullSubcategory (fun X : Comma L R => IsIso X.hom)

/-- The projection from the iso-comma to its left factor. -/
noncomputable def S1836IsoCommaFst {A : Type u} {B : Type v} {C : Type w}
    [Category A] [Category B] [Category C]
    (L : A ⥤ C) (R : B ⥤ C) : S1836IsoComma L R ⥤ A :=
  ObjectProperty.ι (fun X : Comma L R => IsIso X.hom) ⋙ Comma.fst L R

/-- The projection from the iso-comma to its right factor. -/
noncomputable def S1836IsoCommaSnd {A : Type u} {B : Type v} {C : Type w}
    [Category A] [Category B] [Category C]
    (L : A ⥤ C) (R : B ⥤ C) : S1836IsoComma L R ⥤ B :=
  ObjectProperty.ι (fun X : Comma L R => IsIso X.hom) ⋙ Comma.snd L R

/-- The canonical 2-commuting isomorphism of the fibre-level square. -/
noncomputable def S1836IsoCommaNatIso {A : Type u} {B : Type v} {C : Type w}
    [Category A] [Category B] [Category C]
    (L : A ⥤ C) (R : B ⥤ C) :
    Iso (S1836IsoCommaFst L R ⋙ L) (S1836IsoCommaSnd L R ⋙ R) :=
  NatIso.ofComponents
    (fun X => by
      haveI : IsIso X.obj.hom := X.2
      exact (show L.obj X.obj.left ≅ R.obj X.obj.right from asIso X.obj.hom))
    (fun {X Y} f => by
      dsimp
      exact f.hom.w)

/-- The two projections of the iso-comma are jointly faithful. -/
theorem S1836IsoComma_hom_ext {A : Type u} {B : Type v} {C : Type w}
    [Category A] [Category B] [Category C]
    (L : A ⥤ C) (R : B ⥤ C) {X Y : S1836IsoComma L R} (f g : X ⟶ Y)
    (h1 : (S1836IsoCommaFst L R).map f = (S1836IsoCommaFst L R).map g)
    (h2 : (S1836IsoCommaSnd L R).map f = (S1836IsoCommaSnd L R).map g) :
    f = g := by
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · exact h1
  · exact h2

/-! ## 2. The equivalence A ~ IsoComma L (id C) -/

/-- The object of the iso-comma IsoComma L (id C) attached to a : A. -/
noncomputable def S1836IsoCommaRightIdObj {A : Type u} {C : Type w}
    [Category A] [Category C] (L : A ⥤ C) (a : A) :
    S1836IsoComma L (𝟭 C) :=
  ⟨Comma.mk a (L.obj a) (𝟙 (L.obj a)), IsIso.id _⟩

/-- The functor a |-> (a, L a, id) from A to IsoComma L (id C). -/
noncomputable def S1836IsoCommaRightIdFun {A : Type u} {C : Type w}
    [Category A] [Category C] (L : A ⥤ C) :
    A ⥤ S1836IsoComma L (𝟭 C) where
  obj := S1836IsoCommaRightIdObj L
  map {a a'} f := ObjectProperty.homMk (CommaMorphism.mk f (L.map f) (by
    dsimp [S1836IsoCommaRightIdObj]
    simp))
  map_id a := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · change L.map (𝟙 a) = 𝟙 (L.obj a)
      simp
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · change L.map (f ≫ g) = L.map f ≫ L.map g
      simp

instance S1836IsoCommaRightIdFun_faithful {A : Type u} {C : Type w}
    [Category A] [Category C] (L : A ⥤ C) :
    (S1836IsoCommaRightIdFun L).Faithful where
  map_injective {a a'} {f g} h :=
    congrArg (fun φ => φ.hom.left) h

instance S1836IsoCommaRightIdFun_full {A : Type u} {C : Type w}
    [Category A] [Category C] (L : A ⥤ C) :
    (S1836IsoCommaRightIdFun L).Full where
  map_surjective {a a'} φ := by
    refine ⟨φ.hom.left, ?_⟩
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · dsimp [S1836IsoCommaRightIdFun, S1836IsoCommaRightIdObj]
      have hw := φ.hom.w
      dsimp [S1836IsoCommaRightIdFun, S1836IsoCommaRightIdObj] at hw
      simpa using hw

instance S1836IsoCommaRightIdFun_essSurj {A : Type u} {C : Type w}
    [Category A] [Category C] (L : A ⥤ C) :
    (S1836IsoCommaRightIdFun L).EssSurj where
  mem_essImage X := by
    haveI hX : IsIso X.obj.hom := X.2
    let r : L.obj X.obj.left ≅ (𝟭 C).obj X.obj.right := asIso X.obj.hom
    let e : (S1836IsoCommaRightIdFun L).obj X.obj.left ≅ X :=
      ObjectProperty.isoMk (P := fun Y : Comma L (𝟭 C) => IsIso Y.hom)
        (Comma.isoMk (L₁ := L) (R₁ := 𝟭 C)
          (X := ((S1836IsoCommaRightIdFun L).obj X.obj.left).obj) (Y := X.obj)
          (Iso.refl _) r (by
            dsimp only [r, S1836IsoCommaRightIdFun, S1836IsoCommaRightIdObj]
            simp))
    exact ⟨X.obj.left, ⟨e⟩⟩

instance S1836IsoCommaRightIdFun_isEquivalence {A : Type u} {C : Type w}
    [Category A] [Category C] (L : A ⥤ C) :
    (S1836IsoCommaRightIdFun L).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The fibre-level equivalence A ~ IsoComma L (id C). -/
noncomputable def S1836IsoCommaRightIdEquiv {A : Type u} {C : Type w}
    [Category A] [Category C] (L : A ⥤ C) :
    A ≌ S1836IsoComma L (𝟭 C) :=
  (S1836IsoCommaRightIdFun L).asEquivalence

/-! ## 3. The equivalence B ~ IsoComma (id C) L -/

/-- The object of the iso-comma IsoComma (id C) L attached to b : B. -/
noncomputable def S1836IsoCommaLeftIdObj {B : Type v} {C : Type w}
    [Category B] [Category C] (L : B ⥤ C) (b : B) :
    S1836IsoComma (𝟭 C) L :=
  ⟨Comma.mk (L.obj b) b (𝟙 (L.obj b)), IsIso.id _⟩

/-- The functor b |-> (L b, b, id) from B to IsoComma (id C) L. -/
noncomputable def S1836IsoCommaLeftIdFun {B : Type v} {C : Type w}
    [Category B] [Category C] (L : B ⥤ C) :
    B ⥤ S1836IsoComma (𝟭 C) L where
  obj := S1836IsoCommaLeftIdObj L
  map {b b'} f := ObjectProperty.homMk (CommaMorphism.mk (L.map f) f (by
    dsimp [S1836IsoCommaLeftIdObj]
    simp))
  map_id b := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · change L.map (𝟙 b) = 𝟙 (L.obj b)
      simp
    · rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · change L.map (f ≫ g) = L.map f ≫ L.map g
      simp
    · rfl

instance S1836IsoCommaLeftIdFun_faithful {B : Type v} {C : Type w}
    [Category B] [Category C] (L : B ⥤ C) :
    (S1836IsoCommaLeftIdFun L).Faithful where
  map_injective {b b'} {f g} h :=
    congrArg (fun φ => φ.hom.right) h

instance S1836IsoCommaLeftIdFun_full {B : Type v} {C : Type w}
    [Category B] [Category C] (L : B ⥤ C) :
    (S1836IsoCommaLeftIdFun L).Full where
  map_surjective {b b'} φ := by
    refine ⟨φ.hom.right, ?_⟩
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · dsimp [S1836IsoCommaLeftIdFun, S1836IsoCommaLeftIdObj]
      have hw := φ.hom.w
      dsimp [S1836IsoCommaLeftIdFun, S1836IsoCommaLeftIdObj] at hw
      simpa using hw.symm
    · rfl

instance S1836IsoCommaLeftIdFun_essSurj {B : Type v} {C : Type w}
    [Category B] [Category C] (L : B ⥤ C) :
    (S1836IsoCommaLeftIdFun L).EssSurj where
  mem_essImage X := by
    haveI hX : IsIso X.obj.hom := X.2
    let l : L.obj X.obj.right ≅ (𝟭 C).obj X.obj.left := (asIso X.obj.hom).symm
    let e : (S1836IsoCommaLeftIdFun L).obj X.obj.right ≅ X :=
      ObjectProperty.isoMk (P := fun Y : Comma (𝟭 C) L => IsIso Y.hom)
        (Comma.isoMk (L₁ := 𝟭 C) (R₁ := L)
          (X := ((S1836IsoCommaLeftIdFun L).obj X.obj.right).obj) (Y := X.obj)
          l (Iso.refl _) (by
            dsimp only [l, S1836IsoCommaLeftIdFun, S1836IsoCommaLeftIdObj]
            simp))
    exact ⟨X.obj.right, ⟨e⟩⟩

instance S1836IsoCommaLeftIdFun_isEquivalence {B : Type v} {C : Type w}
    [Category B] [Category C] (L : B ⥤ C) :
    (S1836IsoCommaLeftIdFun L).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The fibre-level equivalence B ~ IsoComma (id C) L. -/
noncomputable def S1836IsoCommaLeftIdEquiv {B : Type v} {C : Type w}
    [Category B] [Category C] (L : B ⥤ C) :
    B ≌ S1836IsoComma (𝟭 C) L :=
  (S1836IsoCommaLeftIdFun L).asEquivalence

/-! ## 4. The stack-level datum -/

/-- The fibre-level realization of the pseudopullback for a fixed two-pullback
cover P: at every test scheme, the fibre of P is equivalent to the iso-comma
of the two cospan maps, compatibly with the two projections. -/
structure S1836FiberRealization {A B C : S1728Cover}
    {f : S1728CoverMap A C} {g : S1728CoverMap B C}
    (P : S1832TwoPullback f g) where
  /-- The equivalence between the fibre of the apex stack and the iso-comma. -/
  isoCommaEquiv : ∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
    ↑(P.apex.source.fiber.obj U) ≌
      S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor
  /-- The equivalence is compatible with the first projection. -/
  toA_compat : ∀ U,
    Iso ((isoCommaEquiv U).functor ⋙
        S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor)
      ((P.toA).map.app U).toFunctor
  /-- The equivalence is compatible with the second projection. -/
  toB_compat : ∀ U,
    Iso ((isoCommaEquiv U).functor ⋙
        S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor)
      ((P.toB).map.app U).toFunctor

/-- The actual pseudopullback-stack datum: a two-pullback cover P (so an
actual EtaleStackOverField with its IsStack proof and its representably
finite-etale structure map) together with a fibre realization of the iso-comma. -/
structure S1836PseudopullbackStackDatum {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) where
  /-- The two-pullback cover of S1832. -/
  twoPullback : S1832TwoPullback f g
  /-- Its source stack realizes the iso-comma fibres. -/
  realization : S1836FiberRealization twoPullback

namespace S1836PseudopullbackStackDatum

variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}
  (D : S1836PseudopullbackStackDatum f g)

/-- The apex cover. -/
def cover : S1728Cover :=
  D.twoPullback.apex

/-- The actual stack carried by the pseudopullback. -/
def stack : EtaleStackOverField S1726K :=
  D.cover.source

/-- The structure map of the pseudopullback to the orbicurve stack. -/
def structureMap : D.stack.Hom S1726Orbicurve.stack :=
  D.cover.map

/-- The pseudopullback stack is an actual etale stack. -/
theorem stack_isStack :
    D.stack.fiber.IsStack (SchemeOverField.etaleTopology S1726K) :=
  D.stack.isStack

/-- **The structure map is representably finite etale.** -/
def structureMap_finiteEtale :
    EtaleStackFiniteEtaleMorphism D.structureMap :=
  D.cover.finiteEtale

/-- The fibre of the pseudopullback stack is the iso-comma category. -/
theorem fiber_isoComma (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    Nonempty (↑(D.stack.fiber.obj U) ≌
      S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor) :=
  ⟨D.realization.isoCommaEquiv U⟩

/-- The fibre equivalence is compatible with the first projection. -/
def fiber_toA (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    Iso ((D.realization.isoCommaEquiv U).functor ⋙
        S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor)
      ((D.twoPullback.toA).map.app U).toFunctor :=
  D.realization.toA_compat U

/-- The fibre equivalence is compatible with the second projection. -/
def fiber_toB (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    Iso ((D.realization.isoCommaEquiv U).functor ⋙
        S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor)
      ((D.twoPullback.toB).map.app U).toFunctor :=
  D.realization.toB_compat U

/-- The datum gives a genuine pullback in the actual 2-isomorphism quotient. -/
theorem hasPullback (D : S1836PseudopullbackStackDatum f g) :
    HasPullback (S1832Q f) (S1832Q g) :=
  S1832HasPullback_of_twoPullback D.twoPullback

end S1836PseudopullbackStackDatum

/-! ## 5. The two-pullback covers with an identity leg -/

/-- The two-pullback cover of the cospan (f, id_C), with apex A. -/
noncomputable def S1836TwoPullbackIdRight {A C : S1728Cover} (f : S1728CoverMap A C) :
    S1832TwoPullback f (S1641CoverMapId C) where
  apex := A
  toA := S1641CoverMapId A
  toB := f
  commutes := (S1728LeftUnitorIso f).trans (S1728RightUnitorIso f).symm
  lift := fun _ c => c.toA
  liftToA := fun _ c => S1728RightUnitorIso c.toA
  liftToB := fun _ c => c.commutes.trans (S1728RightUnitorIso c.toB)
  uniq := fun _ _ _ h1 _ => by
    obtain ⟨e⟩ := h1
    exact ⟨(S1728RightUnitorIso _).symm.trans e⟩

/-- The fibre realization for the cospan (f, id_C), via the fibre-level
equivalence A ~ IsoComma f (id C). -/
noncomputable def S1836FiberRealizationIdRight {A C : S1728Cover}
    (f : S1728CoverMap A C) :
    S1836FiberRealization (S1836TwoPullbackIdRight f) where
  isoCommaEquiv U := S1836IsoCommaRightIdEquiv ((f.map.app U).toFunctor)
  toA_compat U := Iso.refl _
  toB_compat U := Iso.refl _

/-- The full pseudopullback-stack datum for (f, id_C). -/
noncomputable def S1836PseudopullbackStackDatum_id_right {A C : S1728Cover}
    (f : S1728CoverMap A C) :
    S1836PseudopullbackStackDatum f (S1641CoverMapId C) :=
  ⟨S1836TwoPullbackIdRight f, S1836FiberRealizationIdRight f⟩

/-- The two-pullback cover of the cospan (id_C, g), with apex B. -/
noncomputable def S1836TwoPullbackIdLeft {B C : S1728Cover} (g : S1728CoverMap B C) :
    S1832TwoPullback (S1641CoverMapId C) g where
  apex := B
  toA := g
  toB := S1641CoverMapId B
  commutes := (S1728RightUnitorIso g).trans (S1728LeftUnitorIso g).symm
  lift := fun _ c => c.toB
  liftToA := fun _ c => c.commutes.symm.trans (S1728RightUnitorIso c.toA)
  liftToB := fun _ c => S1728RightUnitorIso c.toB
  uniq := fun _ _ _ _ h2 => by
    obtain ⟨e⟩ := h2
    exact ⟨(S1728RightUnitorIso _).symm.trans e⟩

/-- The fibre realization for the cospan (id_C, g), via the fibre-level
equivalence B ~ IsoComma (id C) g. -/
noncomputable def S1836FiberRealizationIdLeft {B C : S1728Cover}
    (g : S1728CoverMap B C) :
    S1836FiberRealization (S1836TwoPullbackIdLeft g) where
  isoCommaEquiv U := S1836IsoCommaLeftIdEquiv ((g.map.app U).toFunctor)
  toA_compat U := Iso.refl _
  toB_compat U := Iso.refl _

/-- The full pseudopullback-stack datum for (id_C, g). -/
noncomputable def S1836PseudopullbackStackDatum_id_left {B C : S1728Cover}
    (g : S1728CoverMap B C) :
    S1836PseudopullbackStackDatum (S1641CoverMapId C) g :=
  ⟨S1836TwoPullbackIdLeft g, S1836FiberRealizationIdLeft g⟩

/-! ## 6. The exact first missing statement and consumers -/

/-- **The exact missing stack statement.**  For every cospan of actual
finite-etale cover maps there is a two-pullback cover whose source stack realizes
the iso-comma fibres through the two projections, with its actual IsStack proof
and its representably finite-etale structure map. -/
def S1836FirstMissingPseudopullbackStack : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    Nonempty (S1836PseudopullbackStackDatum f g)

/-- The existence form of the stack realization: for every cospan there is a
two-pullback cover P with a fibre realization. -/
def S1836FirstMissingStackRealization : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    ∃ P : S1832TwoPullback f g, Nonempty (S1836FiberRealization P)

/-- The realization form implies the datum form. -/
theorem S1836FirstMissing_of_realization
    (h : S1836FirstMissingStackRealization) :
    S1836FirstMissingPseudopullbackStack := by
  intro A B C f g
  obtain ⟨P, hP⟩ := h A B C f g
  exact ⟨P, Classical.choice hP⟩

/-- The datum form implies the realization form. -/
theorem S1836Realization_of_firstMissing
    (h : S1836FirstMissingPseudopullbackStack) :
    S1836FirstMissingStackRealization := by
  intro A B C f g
  obtain ⟨D⟩ := h A B C f g
  exact ⟨D.twoPullback, ⟨D.realization⟩⟩

/-- The datum form and the realization form are equivalent. -/
theorem S1836FirstMissing_iff_realization :
    S1836FirstMissingPseudopullbackStack ↔ S1836FirstMissingStackRealization :=
  ⟨S1836Realization_of_firstMissing, S1836FirstMissing_of_realization⟩

/-- **The stack statement implies S1832's categorical first missing.** -/
theorem S1836FirstMissing_to_S1832
    (h : S1836FirstMissingPseudopullbackStack) :
    S1832FirstMissingPullback := by
  intro A B C f g
  exact ⟨(Classical.choice (h A B C f g)).twoPullback⟩

/-- **The stack statement implies actual pullbacks** in the 2-isomorphism
quotient of the finite-etale cover category. -/
theorem S1836HasPullbacks
    (h : S1836FirstMissingPseudopullbackStack) :
    @HasPullbacks S1728Cover S1728ActualCategory11 :=
  S1832HasPullbacks_of_squares (S1836FirstMissing_to_S1832 h)

/-- The stack statement feeds S1762's finite-limit field. -/
theorem S1836HasFiniteLimitsActual
    (h : S1836FirstMissingPseudopullbackStack) :
    S1736ObligationFiniteLimits (F := S1762K) (X := S1762X) :=
  S1832HasFiniteLimitsActual (S1836FirstMissing_to_S1832 h)

/-- The stack statement, together with the three other S1762 inputs, gives the
actual PreGaloisCategory. -/
theorem S1836PreGaloisCategoryOfStack
    (h : S1836FirstMissingPseudopullbackStack)
    (hCoprod : S1762FiniteCoproductObligationActual)
    (hQuot : S1762FiniteGroupQuotientObligationActual)
    (hMono : S1762MonoDirectSummandObligationActual) :
    S1736ActualPreGaloisObligation (F := S1762K) (X := S1762X) :=
  S1832PreGaloisCategoryOfSquares (S1836FirstMissing_to_S1832 h)
    hCoprod hQuot hMono

/-- The identity-leg cases are unconditional inhabitants of the datum; this
records non-vacuity of the missing statement. -/
theorem S1836IdentityLegsNonvacuous :
    (∀ (A C : S1728Cover) (f : S1728CoverMap A C),
        Nonempty (S1836PseudopullbackStackDatum f (S1641CoverMapId C))) ∧
    (∀ (B C : S1728Cover) (g : S1728CoverMap B C),
        Nonempty (S1836PseudopullbackStackDatum (S1641CoverMapId C) g)) :=
  ⟨fun A C f => ⟨S1836PseudopullbackStackDatum_id_right f⟩,
    fun B C g => ⟨S1836PseudopullbackStackDatum_id_left g⟩⟩

/-- In the identity-right case the constructed stack is literally the source of
the other cover and the structure map is literally its finite-etale cover map. -/
theorem S1836Datum_id_right_stack {A C : S1728Cover} (f : S1728CoverMap A C) :
    (S1836PseudopullbackStackDatum_id_right f).stack = A.source := rfl

/-- In the identity-right case the structure map is the cover's own map. -/
theorem S1836Datum_id_right_structureMap {A C : S1728Cover}
    (f : S1728CoverMap A C) :
    (S1836PseudopullbackStackDatum_id_right f).structureMap = A.map := rfl

/-- In the identity-left case the constructed stack is literally the source of
the other cover. -/
theorem S1836Datum_id_left_stack {B C : S1728Cover} (g : S1728CoverMap B C) :
    (S1836PseudopullbackStackDatum_id_left g).stack = B.source := rfl

/-- In the identity-left case the structure map is the cover's own map. -/
theorem S1836Datum_id_left_structureMap {B C : S1728Cover}
    (g : S1728CoverMap B C) :
    (S1836PseudopullbackStackDatum_id_left g).structureMap = B.map := rfl

/-! ## 7. Checks and axiom audit -/

#check S1836IsoComma
#check S1836IsoCommaFst
#check S1836IsoCommaSnd
#check S1836IsoCommaNatIso
#check S1836IsoComma_hom_ext
#check S1836IsoCommaRightIdEquiv
#check S1836IsoCommaLeftIdEquiv
#check S1836FiberRealization
#check S1836PseudopullbackStackDatum
#check S1836PseudopullbackStackDatum.stack
#check S1836PseudopullbackStackDatum.structureMap
#check S1836PseudopullbackStackDatum.stack_isStack
#check S1836PseudopullbackStackDatum.structureMap_finiteEtale
#check S1836PseudopullbackStackDatum.fiber_isoComma
#check S1836TwoPullbackIdRight
#check S1836FiberRealizationIdRight
#check S1836PseudopullbackStackDatum_id_right
#check S1836TwoPullbackIdLeft
#check S1836FiberRealizationIdLeft
#check S1836PseudopullbackStackDatum_id_left
#check S1836FirstMissingPseudopullbackStack
#check S1836FirstMissingStackRealization
#check S1836FirstMissing_iff_realization
#check S1836FirstMissing_to_S1832
#check S1836HasPullbacks
#check S1836HasFiniteLimitsActual
#check S1836PreGaloisCategoryOfStack
#check S1836IdentityLegsNonvacuous
#check S1836Datum_id_right_stack
#check S1836Datum_id_right_structureMap
#check S1836Datum_id_left_stack
#check S1836Datum_id_left_structureMap

#print axioms S1836IsoCommaRightIdEquiv
#print axioms S1836IsoCommaLeftIdEquiv
#print axioms S1836IsoCommaNatIso
#print axioms S1836IsoComma_hom_ext
#print axioms S1836TwoPullbackIdRight
#print axioms S1836FiberRealizationIdRight
#print axioms S1836PseudopullbackStackDatum_id_right
#print axioms S1836TwoPullbackIdLeft
#print axioms S1836FiberRealizationIdLeft
#print axioms S1836PseudopullbackStackDatum_id_left
#print axioms S1836PseudopullbackStackDatum.stack_isStack
#print axioms S1836PseudopullbackStackDatum.structureMap_finiteEtale
#print axioms S1836FirstMissing_iff_realization
#print axioms S1836FirstMissing_to_S1832
#print axioms S1836HasPullbacks
#print axioms S1836HasFiniteLimitsActual
#print axioms S1836PreGaloisCategoryOfStack
#print axioms S1836IdentityLegsNonvacuous

end LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
