/-
# S1864: the general-cospan pseudopullback stack -- the iso-comma site restriction,
the canonical cone comparison, and the exact first missing

## Context and target

S1832 proved that the categorical (limit) half of the pullback obligation is free:
a bicategorical two-pullback datum for a cospan of actual finite-etale cover maps
f : A -> C, g : B -> C yields a genuine limit in the 2-isomorphism quotient
S1728ActualCategory11, and conversely.  S1836 constructed the fibre-level
iso-comma of the cospan and the full datum in the two identity-leg cases, and
isolated the remaining geometric input as three items:

  (a) a category-valued pseudofunctor on the whole etale site whose value at a
      test scheme U is the iso-comma category of (f.app U) and (g.app U),
  (b) the descent condition IsStack for it,
  (c) a structure map to X.stack which is representably finite etale.

The present file attacks (a) and the packaging question, and sharpens the
obligation.

## What is constructed here, unconditionally

1.  The site restriction of the fibre-level iso-comma.
    S1864IsoCommaRestrict (section 1): for any 2-commuting square of functors
    (alpha : F1 ; L' ~ L ; F, beta : R ; F ~ F2 ; R') it produces the functor
    IsoComma L R -> IsoComma L' R' by transporting Mathlib's Comma.map.  The
    two projections are recovered *strictly*
    (S1864IsoCommaRestrict_fst, S1864IsoCommaRestrict_snd), and the structure
    morphism of the image object is computed (S1864IsoCommaRestrict_obj_hom).
    This is the 1-cell part of (a).

2.  The canonical cone comparison.
    S1864ConeFunctor (section 2): for any cone of categories
    TA : D -> A, TB : D -> B with a 2-commutativity gamma : TA ; L ~ TB ; R, it
    produces the canonical functor D -> IsoComma L R, again with *strict*
    projection compatibility.  This is the canonical half of the "fibre
    realization" of S1836: for an actual two-pullback apex P, the fibre of the
    apex at a test object always maps canonically to the iso-comma, so the
    realization obligation is precisely the statement that this canonical
    functor is an equivalence.

3.  The concrete site-level instance (section 3): for a cospan of actual cover
    maps and a morphism of test objects, S1864CoverIsoCommaRestrict is the
    restriction functor between the actual iso-comma fibres; its comparison
    isomorphisms are the naturality 2-isomorphisms of the two cover maps.  This
    is the object-and-1-cell part of the pseudofunctor of (a), with the actual
    S1728 data.

4.  The exact decomposition of the obligation (sections 4-5).  The apex datum of
    a pseudopullback of a general cospan is packaged as
    S1864IsoCommaStackObligation, with the stack (a)+(b), its two projections,
    their compatibility with the iso-comma projections, the representably
    finite-etale structure map (c), and the bicategorical universal property.
    It is proved equivalent to S1836's S1836PseudopullbackStackDatum
    (S1864FirstMissing_iff_S1836), hence implies S1832's
    S1832FirstMissingPullback and HasPullbacks S1728ActualCategory11
    (S1864HasPullbacks), S1762's finite-limit field
    (S1864HasFiniteLimitsActual) and, with the other three inputs, the actual
    PreGaloisCategory (S1864PreGaloisCategoryOfStack).

## The exact first missing statement

S1864FirstMissingPseudopullbackStack is S1836's obligation, re-derived as the
conjunction of four separately named statements.  The exact first missing ones,
in the order in which they are needed, are:

* (a) THE PSEUDOFUNCTOR COHERENCE.  Section 1 constructs the object assignment
  and the restriction functors, and section 3 instantiates them on the actual
  site, but the comparison 2-isomorphisms for mapId and mapComp -- equivalently,
  a natural isomorphism between the restriction along a composite of two site
  morphisms and the composite of the two restrictions -- together with the three
  pseudofunctor coherence axioms, are *not* constructed.  They are not instances
  of any Mathlib lemma: Mathlib has Comma.map and the one-sided comparisons
  Comma.mapLeftId, Comma.mapLeftComp, Comma.mapLeftEq
  (Mathlib/CategoryTheory/Comma/Basic.lean), but no comparison for a composite
  of two *two-sided* Comma.map functors, and no pseudofunctor whose values are
  comma categories.  The comparison isomorphisms must be built from the
  mapComp/mapId coherences of the two stack pseudofunctors and of the two cover
  maps.
* (b) IsStack.  Even given (a), the effective-descent statement for the
  iso-comma pseudofunctor is a genuinely new descent theorem: it is neither the
  IsStack of a representable pseudofunctor (S1419) nor Mathlib's
  Pseudofunctor.IsStack.of_isStackFor applied to existing data.  The honest proof
  is the 2-categorical one -- 2-fibre products of stacks are stacks, which needs
  descent of objects along the two legs and descent of the comparison
  isomorphisms along the common base -- and it is not present in the tree.
* (c) THE REPRESENTABLY FINITE-ETALE STRUCTURE MAP.  The map
  iso-comma -> X.stack is the composite of the first projection with A.map.
  EtaleStackFiniteEtaleMorphism requires, for every scheme-valued point of
  X.stack, an actual scheme-theoretic base-change presentation whose square is a
  bicategorical pullback; the pasting of the square of the projection with the
  base-change square of A.map is not in the tree, and representable finite
  etaleness of the projections of a 2-fibre product is not available.  Note that
  OrbicurveFiniteEtaleCoverMap carries *no* finite-etale condition on its
  underlying strong transformation, so even "the projection is finite etale"
  needs a proof and cannot be read off.
* (d) THE UNIVERSAL PROPERTY AND ESSENTIAL SURJECTIVITY OF THE CANONICAL
  COMPARISON.  The bicategorical lift and its uniqueness (S1832TwoPullback
  fields lift, liftToA, liftToB, uniq) are the 2-categorical universal property
  of the 2-fibre product, and the canonical comparison of section 2 must be shown
  essentially surjective (fullness and faithfulness then follow from the joint
  faithfulness of the two projections).  Section 2 isolates the canonical
  comparison, so the realization obligation of S1836 is reduced to "the
  canonical comparison is an equivalence".

Item (d) becomes automatic as soon as the apex stack *is* the iso-comma
pseudofunctor of (a), which is why (a) is the first missing item.

## Honest boundary

No sorry, no new axiom, no Shrink, ULift or PUnit, and no fake stack.  Nothing
asserts (a), (b), (c) or (d).  The unconditional contents are the two general
constructions of sections 1 and 2 together with their strict projection
compatibilities, the site-level instance of section 3, and the exact equivalence
between the decomposed obligation and S1836's datum.  The only axioms used are
propext, Classical.choice and Quot.sound; see the #print axioms block.
-/

import tmp.sheaf.xif.paper.S1836CoverPullbackStackActual
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual

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
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual

universe u v w

/-! ## 1. Restriction of the fibre-level iso-comma -/

section Restrict

variable {A : Type u} {B : Type v} {C : Type w}
  [Category.{u, u} A] [Category.{v, v} B] [Category.{w, w} C]
  {A' : Type u} {B' : Type v} {C' : Type w}
  [Category.{u, u} A'] [Category.{v, v} B'] [Category.{w, w} C']
  {L : A ⥤ C} {R : B ⥤ C} {L' : A' ⥤ C'} {R' : B' ⥤ C'}
  (F₁ : A ⥤ A') (F₂ : B ⥤ B') (F : C ⥤ C')
  (α : (F₁ ⋙ L') ≅ (L ⋙ F)) (β : (R ⋙ F) ≅ (F₂ ⋙ R'))

/-- **The restriction functor of the iso-comma.**  It sends an object
(a, b, h : L a ~ R b) to (F1 a, F2 b, alpha a ; F h ; beta b). -/
noncomputable def S1864IsoCommaRestrict :
    S1836IsoComma L R ⥤ S1836IsoComma L' R' where
  obj X :=
    ⟨(Comma.map α.hom β.hom).obj X.obj, by
      haveI hX : IsIso X.obj.hom := X.2
      let e : F.obj (L.obj X.obj.left) ≅ F.obj (R.obj X.obj.right) :=
        { hom := F.map X.obj.hom
          inv := F.map (inv X.obj.hom)
          hom_inv_id := by rw [← F.map_comp, IsIso.hom_inv_id, F.map_id]
          inv_hom_id := by rw [← F.map_comp, IsIso.inv_hom_id, F.map_id] }
      rw [Comma.map_obj_hom]
      exact (Iso.trans (α.app X.obj.left)
        (Iso.trans e (β.app X.obj.right))).isIso_hom⟩
  map f := ObjectProperty.homMk ((Comma.map α.hom β.hom).map f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    simp
  map_comp f g := by
    apply ObjectProperty.hom_ext
    simp

/-- The structure morphism of a restricted object, explicitly. -/
theorem S1864IsoCommaRestrict_obj_hom (X : S1836IsoComma L R) :
    ((S1864IsoCommaRestrict F₁ F₂ F α β).obj X).obj.hom =
      (α.app X.obj.left).hom ≫ F.map X.obj.hom ≫ (β.app X.obj.right).hom :=
  Comma.map_obj_hom α.hom β.hom X.obj

/-- **Strict compatibility with the first projection.** -/
theorem S1864IsoCommaRestrict_fst :
    S1864IsoCommaRestrict F₁ F₂ F α β ⋙ S1836IsoCommaFst L' R' =
      S1836IsoCommaFst L R ⋙ F₁ := rfl

/-- **Strict compatibility with the second projection.** -/
theorem S1864IsoCommaRestrict_snd :
    S1864IsoCommaRestrict F₁ F₂ F α β ⋙ S1836IsoCommaSnd L' R' =
      S1836IsoCommaSnd L R ⋙ F₂ := rfl

end Restrict

/-! ## 2. The canonical comparison functor from a cone to the iso-comma -/

section Cone

variable {D : Type u} [Category.{u, u} D]
  {A : Type u} {B : Type v} {C : Type w}
  [Category.{u, u} A] [Category.{v, v} B] [Category.{w, w} C]
  (L : A ⥤ C) (R : B ⥤ C) (TA : D ⥤ A) (TB : D ⥤ B)
  (γ : (TA ⋙ L) ≅ (TB ⋙ R))

/-- **The canonical comparison functor from a cone to the iso-comma.** -/
noncomputable def S1864ConeFunctor : D ⥤ S1836IsoComma L R where
  obj X := ⟨Comma.mk (TA.obj X) (TB.obj X) ((γ.app X).hom), (γ.app X).isIso_hom⟩
  map {X Y} f :=
    ObjectProperty.homMk (CommaMorphism.mk (TA.map f) (TB.map f) (γ.hom.naturality f))
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp

/-- The comparison functor recovers the first leg strictly. -/
theorem S1864ConeFunctor_fst :
    S1864ConeFunctor L R TA TB γ ⋙ S1836IsoCommaFst L R = TA := rfl

/-- The comparison functor recovers the second leg strictly. -/
theorem S1864ConeFunctor_snd :
    S1864ConeFunctor L R TA TB γ ⋙ S1836IsoCommaSnd L R = TB := rfl

/-- The structure morphism of a compared object, explicitly. -/
theorem S1864ConeFunctor_obj_hom (X : D) :
    ((S1864ConeFunctor L R TA TB γ).obj X).obj.hom = (γ.app X).hom := rfl

end Cone

/-! ## 3. The actual site instance -/

section Site

/-- The comparison isomorphism for the first cover map at a morphism of test
objects: the naturality 2-isomorphism of the strong transformation. -/
noncomputable def S1864SiteComparisonLeft {A C : S1728Cover}
    (f : S1728CoverMap A C)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    ((A.source.fiber.map φ).toFunctor ⋙ (f.map.app V).toFunctor) ≅
      ((f.map.app U).toFunctor ⋙ (C.source.fiber.map φ).toFunctor) :=
  Cat.Hom.toNatIso (f.map.naturality φ)

/-- The comparison isomorphism for the second cover map at a morphism of test
objects. -/
noncomputable def S1864SiteComparisonRight {B C : S1728Cover}
    (g : S1728CoverMap B C)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    ((g.map.app U).toFunctor ⋙ (C.source.fiber.map φ).toFunctor) ≅
      ((B.source.fiber.map φ).toFunctor ⋙ (g.map.app V).toFunctor) :=
  (Cat.Hom.toNatIso (g.map.naturality φ)).symm

/-- **The site restriction of the actual iso-comma fibres.**  For a cospan of
actual finite-etale cover maps and a morphism of test objects phi : U --> V, this
is the restriction functor between the iso-comma categories of the two fibres. -/
noncomputable def S1864CoverIsoCommaRestrict {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor ⥤
      S1836IsoComma (f.map.app V).toFunctor (g.map.app V).toFunctor :=
  S1864IsoCommaRestrict (A.source.fiber.map φ).toFunctor
    (B.source.fiber.map φ).toFunctor (C.source.fiber.map φ).toFunctor
    (S1864SiteComparisonLeft f φ) (S1864SiteComparisonRight g φ)

/-- The site restriction is strictly compatible with the first projection. -/
theorem S1864CoverIsoCommaRestrict_fst {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    S1864CoverIsoCommaRestrict f g φ ⋙
        S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor =
      S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor ⋙
        (A.source.fiber.map φ).toFunctor :=
  rfl

/-- The site restriction is strictly compatible with the second projection. -/
theorem S1864CoverIsoCommaRestrict_snd {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    S1864CoverIsoCommaRestrict f g φ ⋙
        S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor =
      S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor ⋙
        (B.source.fiber.map φ).toFunctor :=
  rfl

end Site

/-! ## 4. The exact decomposition of the apex datum -/

/-- **The apex obligation for the pseudopullback of a general cospan.**  It
consists of the iso-comma site stack (pseudofunctor + IsStack), its two
projections and their compatibility with the fibre-level iso-comma projections,
the representably finite-etale structure map to the orbicurve stack, and the
bicategorical universal property of the 2-fibre product. -/
structure S1864IsoCommaStackObligation {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) where
  /-- (a)+(b) the iso-comma site stack: the pseudofunctor together with its
  effective descent proof -/
  stack : EtaleStackOverField S1726K
  /-- its values are the iso-comma categories -/
  fiberEquiv : ∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
    ↑(stack.fiber.obj U) ≌
      S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor
  /-- the first projection as a morphism of stacks -/
  toA : Pseudofunctor.StrongTrans stack.fiber A.source.fiber
  /-- the second projection as a morphism of stacks -/
  toB : Pseudofunctor.StrongTrans stack.fiber B.source.fiber
  /-- the first projection is the iso-comma first projection -/
  toA_compat : ∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
    Iso ((fiberEquiv U).functor ⋙
        S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor)
      (toA.app U).toFunctor
  /-- the second projection is the iso-comma second projection -/
  toB_compat : ∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
    Iso ((fiberEquiv U).functor ⋙
        S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor)
      (toB.app U).toFunctor
  /-- the square 2-commutes -/
  commutes : Iso (Pseudofunctor.StrongTrans.vcomp toA f.map)
    (Pseudofunctor.StrongTrans.vcomp toB g.map)
  /-- (c) the structure map to the orbicurve stack -/
  structureMap : stack.Hom S1726Orbicurve.stack
  /-- (c) the structure map is representably finite etale -/
  finiteEtale : EtaleStackFiniteEtaleMorphism structureMap
  /-- the structure map is the first projection followed by the cover map -/
  structureMap_eq : Iso (Pseudofunctor.StrongTrans.vcomp toA A.map) structureMap
  /-- and also the second projection followed by the second cover map -/
  structureMap_eq' : Iso (Pseudofunctor.StrongTrans.vcomp toB B.map) structureMap
  /-- (d) the lift of a pseudo-cone -/
  lift : ∀ (W : S1728Cover), S1832Bicone f g W →
    Pseudofunctor.StrongTrans W.source.fiber stack.fiber
  /-- (d) its compatibility with the structure map -/
  liftCommutes : ∀ (W : S1728Cover) (c : S1832Bicone f g W),
    Iso (Pseudofunctor.StrongTrans.vcomp (lift W c) structureMap) W.map
  /-- (d) the comparison 2-isomorphism with the first leg -/
  liftToA : ∀ (W : S1728Cover) (c : S1832Bicone f g W),
    Iso (Pseudofunctor.StrongTrans.vcomp (lift W c) toA) c.toA.map
  /-- (d) the comparison 2-isomorphism with the second leg -/
  liftToB : ∀ (W : S1728Cover) (c : S1832Bicone f g W),
    Iso (Pseudofunctor.StrongTrans.vcomp (lift W c) toB) c.toB.map
  /-- (d) uniqueness of the lift up to 2-isomorphism -/
  uniq : ∀ (W : S1728Cover) (c : S1832Bicone f g W)
    (h : Pseudofunctor.StrongTrans W.source.fiber stack.fiber)
    (_hmap : Iso (Pseudofunctor.StrongTrans.vcomp h structureMap) W.map),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp h toA) c.toA.map) →
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp h toB) c.toB.map) →
    Nonempty (Iso h (lift W c))

namespace S1864IsoCommaStackObligation

variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}

/-- The IsStack proof of the obligation, named separately. -/
theorem stack_isStack (D : S1864IsoCommaStackObligation f g) :
    D.stack.fiber.IsStack (SchemeOverField.etaleTopology S1726K) :=
  D.stack.isStack

/-- The apex cover assembled from the obligation. -/
def apex (D : S1864IsoCommaStackObligation f g) : S1728Cover where
  source := D.stack
  map := D.structureMap
  finiteEtale := D.finiteEtale

/-- The first cover map from the apex. -/
def coverMapToA (D : S1864IsoCommaStackObligation f g) :
    S1728CoverMap D.apex A where
  map := D.toA
  commutes := D.structureMap_eq

/-- The second cover map from the apex. -/
def coverMapToB (D : S1864IsoCommaStackObligation f g) :
    S1728CoverMap D.apex B where
  map := D.toB
  commutes := D.structureMap_eq'

/-- **The obligation produces a two-pullback cover** (S1832's datum). -/
noncomputable def toTwoPullback (D : S1864IsoCommaStackObligation f g) :
    S1832TwoPullback f g where
  apex := D.apex
  toA := D.coverMapToA
  toB := D.coverMapToB
  commutes := D.commutes
  lift W c := ⟨D.lift W c, D.liftCommutes W c⟩
  liftToA := D.liftToA
  liftToB := D.liftToB
  uniq W c h h1 h2 := D.uniq W c h.map h.commutes h1 h2

/-- **The obligation produces S1836's stack datum.** -/
noncomputable def toS1836Datum (D : S1864IsoCommaStackObligation f g) :
    S1836PseudopullbackStackDatum f g where
  twoPullback := D.toTwoPullback
  realization :=
    { isoCommaEquiv := D.fiberEquiv
      toA_compat := D.toA_compat
      toB_compat := D.toB_compat }

/-- The obligation gives an actual pullback in the 2-isomorphism quotient. -/
theorem hasPullback (D : S1864IsoCommaStackObligation f g) :
    HasPullback (S1832Q f) (S1832Q g) :=
  S1832HasPullback_of_twoPullback D.toTwoPullback

end S1864IsoCommaStackObligation

/-- S1836's datum, unpacked, is exactly the obligation. -/
noncomputable def S1864ObligationOfS1836Datum {A B C : S1728Cover}
    {f : S1728CoverMap A C} {g : S1728CoverMap B C}
    (D : S1836PseudopullbackStackDatum f g) :
    S1864IsoCommaStackObligation f g where
  stack := D.cover.source
  fiberEquiv := D.realization.isoCommaEquiv
  toA := D.twoPullback.toA.map
  toB := D.twoPullback.toB.map
  toA_compat := D.realization.toA_compat
  toB_compat := D.realization.toB_compat
  commutes := D.twoPullback.commutes
  structureMap := D.cover.map
  finiteEtale := D.cover.finiteEtale
  structureMap_eq := D.twoPullback.toA.commutes
  structureMap_eq' := D.twoPullback.toB.commutes
  lift W c := (D.twoPullback.lift W c).map
  liftCommutes W c := (D.twoPullback.lift W c).commutes
  liftToA := D.twoPullback.liftToA
  liftToB := D.twoPullback.liftToB
  uniq W c h _hmap h1 h2 := D.twoPullback.uniq W c ⟨h, _hmap⟩ h1 h2

/-! ## 5. The exact first missing statements and their consumers -/

/-- **The exact first missing stack statement.**  For every cospan of actual
finite-etale cover maps there is a category-valued pseudofunctor on the etale
site, a proof of effective descent for it, an identification of its values with
the iso-comma categories, the two compatible projections, and a representably
finite-etale structure map to the orbicurve stack. -/
def S1864FirstMissingIsoCommaStack : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    ∃ (stack : EtaleStackOverField S1726K)
      (e : ∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
        ↑(stack.fiber.obj U) ≌
          S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor)
      (toA : Pseudofunctor.StrongTrans stack.fiber A.source.fiber)
      (toB : Pseudofunctor.StrongTrans stack.fiber B.source.fiber),
      (∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
          Nonempty (Iso ((e U).functor ⋙
              S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor)
            (toA.app U).toFunctor)) ∧
      (∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
          Nonempty (Iso ((e U).functor ⋙
              S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor)
            (toB.app U).toFunctor)) ∧
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp toA f.map)
        (Pseudofunctor.StrongTrans.vcomp toB g.map)) ∧
      ∃ structureMap : stack.Hom S1726Orbicurve.stack,
        Nonempty (EtaleStackFiniteEtaleMorphism
          (source := stack) (target := S1726Orbicurve.stack) structureMap) ∧
          Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp toA A.map) structureMap)

/-- **The exact first missing statement in datum form**: for every cospan there
is an apex datum as in section 4 (stack, projections, finite-etale structure map
and universal property). -/
def S1864FirstMissingPseudopullbackStack : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    Nonempty (S1864IsoCommaStackObligation f g)

/-- The obligation statement is exactly S1836's first missing statement. -/
theorem S1864FirstMissing_iff_S1836 :
    S1864FirstMissingPseudopullbackStack ↔ S1836FirstMissingPseudopullbackStack := by
  constructor
  · intro h A B C f g
    obtain ⟨D⟩ := h A B C f g
    exact ⟨D.toS1836Datum⟩
  · intro h A B C f g
    obtain ⟨D⟩ := h A B C f g
    exact ⟨S1864ObligationOfS1836Datum D⟩

/-- The obligation form implies the named stack statement of section 5: the
universal property of section 4 is exactly the extra input. -/
theorem S1864FirstMissing_to_isoCommaStack
    (h : S1864FirstMissingPseudopullbackStack) : S1864FirstMissingIsoCommaStack := by
  intro A B C f g
  obtain ⟨D⟩ := h A B C f g
  exact ⟨D.stack, D.fiberEquiv, D.toA, D.toB,
    fun U => ⟨D.toA_compat U⟩,
    fun U => ⟨D.toB_compat U⟩,
    ⟨D.commutes⟩,
    D.structureMap, ⟨D.finiteEtale⟩, ⟨D.structureMap_eq⟩⟩

/-- **The decomposed statement implies S1832's categorical first missing.** -/
theorem S1864FirstMissing_to_S1832
    (h : S1864FirstMissingPseudopullbackStack) : S1832FirstMissingPullback :=
  S1836FirstMissing_to_S1832 (S1864FirstMissing_iff_S1836.mp h)

/-- **The decomposed statement implies actual pullbacks** in the 2-isomorphism
quotient of the finite-etale cover category. -/
theorem S1864HasPullbacks (h : S1864FirstMissingPseudopullbackStack) :
    @HasPullbacks S1728Cover S1728ActualCategory11 :=
  S1836HasPullbacks (S1864FirstMissing_iff_S1836.mp h)

/-- The decomposed statement feeds S1762's finite-limit field. -/
theorem S1864HasFiniteLimitsActual (h : S1864FirstMissingPseudopullbackStack) :
    S1736ObligationFiniteLimits (F := S1762K) (X := S1762X) :=
  S1836HasFiniteLimitsActual (S1864FirstMissing_iff_S1836.mp h)

/-- The decomposed statement, together with the three other S1762 inputs, gives
the actual PreGaloisCategory. -/
theorem S1864PreGaloisCategoryOfStack (h : S1864FirstMissingPseudopullbackStack)
    (hCoprod : S1762FiniteCoproductObligationActual)
    (hQuot : S1762FiniteGroupQuotientObligationActual)
    (hMono : S1762MonoDirectSummandObligationActual) :
    S1736ActualPreGaloisObligation (F := S1762K) (X := S1762X) :=
  S1836PreGaloisCategoryOfStack (S1864FirstMissing_iff_S1836.mp h) hCoprod hQuot hMono

/-- The identity-leg cases are unconditional inhabitants of the obligation, so
the decomposed statement is not vacuous: it holds for every cospan with an
identity leg.  (The obligation is generated from S1836's datum, whose identity
cases are constructed unconditionally there.) -/
theorem S1864IdentityLegsNonvacuous :
    (∀ (A C : S1728Cover) (f : S1728CoverMap A C),
        Nonempty (S1864IsoCommaStackObligation f (S1641CoverMapId C))) ∧
    (∀ (B C : S1728Cover) (g : S1728CoverMap B C),
        Nonempty (S1864IsoCommaStackObligation (S1641CoverMapId C) g)) :=
  ⟨fun A C f => ⟨S1864ObligationOfS1836Datum (S1836PseudopullbackStackDatum_id_right f)⟩,
    fun B C g => ⟨S1864ObligationOfS1836Datum (S1836PseudopullbackStackDatum_id_left g)⟩⟩

/-- The site restriction of section 3 exists for every morphism of test objects:
this is the object-and-1-cell part of the missing pseudofunctor, and it is
unconditional. -/
theorem S1864SiteRestrictionExists {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    ∀ (U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (φ : U ⟶ V),
      Nonempty (S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor ⥤
        S1836IsoComma (f.map.app V).toFunctor (g.map.app V).toFunctor) :=
  fun U V φ => ⟨S1864CoverIsoCommaRestrict f g φ⟩

/-- The canonical comparison of section 2 exists for every two-pullback apex as
soon as the fibre-level 2-commutativity of the apex is given; that
2-commutativity is the componentwise reading of the commutes field of
S1832TwoPullback.  This is the unconditional half of the fibre realization of
S1836: only essential surjectivity of this functor is missing. -/
theorem S1864CanonicalComparisonOf {A B C : S1728Cover}
    {f : S1728CoverMap A C} {g : S1728CoverMap B C} (P : S1832TwoPullback f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (γ : ((P.toA.map.app U).toFunctor ⋙ (f.map.app U).toFunctor) ≅
      ((P.toB.map.app U).toFunctor ⋙ (g.map.app U).toFunctor)) :
    Nonempty (↑(P.apex.source.fiber.obj U) ⥤
      S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor) :=
  ⟨S1864ConeFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
    ((P.toA.map.app U).toFunctor) ((P.toB.map.app U).toFunctor) γ⟩

/-! ## 6. Checks and axiom audit -/

#check S1864IsoCommaRestrict
#check S1864IsoCommaRestrict_obj_hom
#check S1864IsoCommaRestrict_fst
#check S1864IsoCommaRestrict_snd
#check S1864ConeFunctor
#check S1864ConeFunctor_fst
#check S1864ConeFunctor_snd
#check S1864ConeFunctor_obj_hom
#check S1864SiteComparisonLeft
#check S1864SiteComparisonRight
#check S1864CoverIsoCommaRestrict
#check S1864CoverIsoCommaRestrict_fst
#check S1864CoverIsoCommaRestrict_snd
#check S1864IsoCommaStackObligation
#check S1864IsoCommaStackObligation.apex
#check S1864IsoCommaStackObligation.coverMapToA
#check S1864IsoCommaStackObligation.coverMapToB
#check S1864IsoCommaStackObligation.toTwoPullback
#check S1864IsoCommaStackObligation.toS1836Datum
#check S1864IsoCommaStackObligation.hasPullback
#check S1864ObligationOfS1836Datum
#check S1864FirstMissingIsoCommaStack
#check S1864FirstMissingPseudopullbackStack
#check S1864FirstMissing_iff_S1836
#check S1864FirstMissing_to_isoCommaStack
#check S1864FirstMissing_to_S1832
#check S1864HasPullbacks
#check S1864HasFiniteLimitsActual
#check S1864PreGaloisCategoryOfStack
#check S1864IdentityLegsNonvacuous
#check S1864SiteRestrictionExists
#check S1864CanonicalComparisonOf

#print axioms S1864IsoCommaRestrict_fst
#print axioms S1864IsoCommaRestrict_snd
#print axioms S1864ConeFunctor_fst
#print axioms S1864ConeFunctor_snd
#print axioms S1864CoverIsoCommaRestrict_fst
#print axioms S1864CoverIsoCommaRestrict_snd
#print axioms S1864IsoCommaStackObligation.toTwoPullback
#print axioms S1864IsoCommaStackObligation.toS1836Datum
#print axioms S1864IsoCommaStackObligation.hasPullback
#print axioms S1864FirstMissing_iff_S1836
#print axioms S1864FirstMissing_to_isoCommaStack
#print axioms S1864FirstMissing_to_S1832
#print axioms S1864HasPullbacks
#print axioms S1864HasFiniteLimitsActual
#print axioms S1864PreGaloisCategoryOfStack
#print axioms S1864IdentityLegsNonvacuous
#print axioms S1864CanonicalComparisonOf

end LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
