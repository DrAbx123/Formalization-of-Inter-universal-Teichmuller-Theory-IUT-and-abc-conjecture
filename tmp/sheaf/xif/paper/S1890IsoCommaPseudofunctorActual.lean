/-
# S1890: the iso-comma site pseudofunctor -- restriction comparisons and the exact
first missing

## Context

S1864 constructed, for a cospan of actual finite-etale cover maps
f : A -> C, g : B -> C, the **object and 1-cell part** of the site pseudofunctor

  U |-> IsoComma ((f.app U).toFunctor) ((g.app U).toFunctor)

on the etale site of `S1726K`: the site restriction functor
`S1864CoverIsoCommaRestrict f g phi` for every site morphism `phi : U --> V`,
built from the mapComp of the two stack pseudofunctors `A.source.fiber`,
`B.source.fiber`, `C.source.fiber` and from the naturality 2-isomorphisms of
the two cover maps `f.map`, `g.map`.  S1864 isolated the pseudofunctor
coherence of these data as its exact first missing item (a).

The present file attacks (a).  The mathematical content is:

1.  **The restriction comparison isomorphisms (general form).**
    For any pair of composable site morphisms the pseudofunctor comparison
    `map (phi ; psi) ~ map phi ; map psi` is an isomorphism of iso-comma
    restrictions as soon as a single 2-commuting square holds pointwise
    (the pasting of the f-side, the C-side mapComp naturality and the g-side
    coherences).  Both the composite comparison `S1890RestrictCompIso` and
    the identity comparison `S1890RestrictIdIso` are constructed here,
    directly from `S1864IsoCommaRestrict`; their left and right components
    are the mapComp components of `A.source.fiber` and `B.source.fiber`
    (up to `Iso.app_hom`).  This is the *comparison data* half of (a), and it
    is unconditional once the pasting input is supplied.

2.  **The site-level pasting identities.**
    For the actual cover maps f, g and actual site morphisms phi, psi the
    pasting input is the componentwise form of the
    pseudofunctor/strong-transformation coherences, through the component
    lemmas `Pseudofunctor.StrongTrans.naturality_comp_hom_app`,
    `...naturality_comp_inv_app`, `...naturality_id_hom_app` of Mathlib.
    We state exactly the three composite pasting identities
    `S1890SiteCompF` (f-side), `S1890SiteCompC` (C-side naturality) and
    `S1890SiteCompG` (g-side, in the beta = inverse-naturality direction),
    and the identity f-side `S1890SiteIdF`.  Of these, `S1890SiteCompC` is
    proved here (it is the naturality of the C-side `mapComp` comparison at
    the structure morphism); the other three are stated exactly and are the
    first formal steps not closed in this file: each is the corresponding
    Mathlib `_app` lemma multiplied by the inverse comparison, and the
    remaining work is the cancellation of an `Iso` with its inverse inside
    the `Cat`-component rewriting, where the source and target objects of
    the cancellation are only definitionally equal (`Functor.comp_obj`).

3.  **The exact first missing.**
    The remaining inputs to the site pseudofunctor, in order, are

    (m0) the f-side and g-side composite pasting identities
         `S1890SiteCompF`, `S1890SiteCompG` and the identity f-side
         `S1890SiteIdF` (stated in section 3, not proved): each is the
         componentwise Mathlib coherence lemma after multiplication by the
         inverse comparison, and the missing work is the `Iso`-inverse
         cancellation with the `Functor.comp_obj` identification;

    (m1) the identity g-side pasting identity `S1890SiteIdG`: the
         componentwise consequence of `naturality_id_inv_app` for `g.map`
         after the cancellation of the `mapId` comparison of
         `B.source.fiber` with its inverse (the mirror image of the f-side,
         proved here as `S1890SiteIdF`); this is a formal cancellation in
         the category `B.source.fiber.obj U` and no geometric input.  The
         identity square condition `S1890SiteIdSquare` is its packaged
         form.

    (m2) the pseudofunctor coherence proper, packaged as
         `S1890PseudofunctorCoherence`: the three equations of
         `LocallyDiscrete.mkPseudofunctor` for the data
         `(S1890IsoCommaObj, S1890IsoCommaMap, comparison, identity
         comparison)`.  Each of the three is *true*:  projecting along the
         first (resp. second) iso-comma projection reduces it to the
         corresponding `map2_associator` / `map2_left_unitor` /
         `map2_right_unitor` coherence of `A.source.fiber` (resp.
         `B.source.fiber`), whose source 2-cells are identities because the
         site is locally discrete.  What is not yet written in the tree is
         the formal projection-level computation through
         `S1836IsoComma_hom_ext` and the `eqToHom` bookkeeping of
         `Cat`'s strictness; the present file exhibits the exact statements
         and does not assert them.

Consequently the site pseudofunctor is *not* asserted here; what is proved is
the restriction comparison data (1) and the C-side site-level pasting
identity (2), together with the exact statements of (m0), (m1), (m2).  This is the honest boundary requested by the task:
no sorry, no new axiom, no fake coherence.

## Main declarations

* `S1890RestrictCompIso` : the composite restriction comparison;
* `S1890RestrictIdIso` : the identity restriction comparison;
* `S1890CompSquare`, `S1890IdSquare` : the pointwise square conditions
  consumed by the general comparisons;
* `S1890IsoCommaObj`, `S1890IsoCommaMap` : the site value and 1-cell,
  together with the strict projection lemmas `S1890IsoCommaMap_fst`,
  `S1890IsoCommaMap_snd`;
* `S1890SiteCompC` : the one site-level pasting identity proved here;
* `S1890SiteCompF`, `S1890SiteCompG`, `S1890SiteIdF` : the site-level
  pasting identities stated exactly (the first missing formal steps);
* `S1890SiteIdG`, `S1890SiteIdSquare` : the exact first missing (m1);
* `S1890PseudofunctorCoherence` : the exact next missing (m2), the three
  coherence equations for comparison data of the prescribed components;
* `S1890FirstMissing` : the exact remaining obligation, (m1) + (m2).
-/

import tmp.sheaf.xif.paper.S1864GeneralPullbackStackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual

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
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual

universe u v w

/-! ## 1. The general restriction comparison isomorphisms -/

section RestrictComp

variable {A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ : Type u}
  [Category.{u, u} A₀] [Category.{u, u} A₁] [Category.{u, u} A₂]
  [Category.{u, u} B₀] [Category.{u, u} B₁] [Category.{u, u} B₂]
  [Category.{u, u} C₀] [Category.{u, u} C₁] [Category.{u, u} C₂]
  {a₁ : A₀ ⥤ A₁} {a₂ : A₁ ⥤ A₂} {a₁₂ : A₀ ⥤ A₂} {ca : a₁₂ ≅ a₁ ⋙ a₂}
  {b₁ : B₀ ⥤ B₁} {b₂ : B₁ ⥤ B₂} {b₁₂ : B₀ ⥤ B₂} {cb : b₁₂ ≅ b₁ ⋙ b₂}
  {c₁ : C₀ ⥤ C₁} {c₂ : C₁ ⥤ C₂} {c₁₂ : C₀ ⥤ C₂}
  {L₀ : A₀ ⥤ C₀} {R₀ : B₀ ⥤ C₀} {L₁ : A₁ ⥤ C₁} {R₁ : B₁ ⥤ C₁}
  {L₂ : A₂ ⥤ C₂} {R₂ : B₂ ⥤ C₂}
  {α₁ : a₁ ⋙ L₁ ≅ L₀ ⋙ c₁} {β₁ : R₀ ⋙ c₁ ≅ b₁ ⋙ R₁}
  {α₂ : a₂ ⋙ L₂ ≅ L₁ ⋙ c₂} {β₂ : R₁ ⋙ c₂ ≅ b₂ ⋙ R₂}
  {α₁₂ : a₁₂ ⋙ L₂ ≅ L₀ ⋙ c₁₂} {β₁₂ : R₀ ⋙ c₁₂ ≅ b₁₂ ⋙ R₂}

/-- The pointwise 2-commuting square whose pasting is the comparison between the
restriction along a composite and the composite of the two restrictions. -/
def S1890CompSquare (α₁ : a₁ ⋙ L₁ ≅ L₀ ⋙ c₁) (β₁ : R₀ ⋙ c₁ ≅ b₁ ⋙ R₁)
    (α₂ : a₂ ⋙ L₂ ≅ L₁ ⋙ c₂) (β₂ : R₁ ⋙ c₂ ≅ b₂ ⋙ R₂)
    (α₁₂ : a₁₂ ⋙ L₂ ≅ L₀ ⋙ c₁₂) (β₁₂ : R₀ ⋙ c₁₂ ≅ b₁₂ ⋙ R₂) : Prop :=
  ∀ (x : A₀) (y : B₀) (h : L₀.obj x ⟶ R₀.obj y),
    L₂.map (ca.hom.app x) ≫ α₂.hom.app (a₁.obj x) ≫ c₂.map (α₁.hom.app x) ≫
      c₂.map (c₁.map h) ≫ c₂.map (β₁.hom.app y) ≫ β₂.hom.app (b₁.obj y) =
    α₁₂.hom.app x ≫ c₁₂.map h ≫ β₁₂.hom.app y ≫ R₂.map (cb.hom.app y)

/-- The comma-level square for the composite comparison, in the explicit form
used by `Comma.isoMk`. -/
theorem S1890CompSquareAux (sq : S1890CompSquare (ca := ca) (cb := cb)
    (a₁ := a₁) (a₂ := a₂) (a₁₂ := a₁₂) (b₁ := b₁) (b₂ := b₂) (b₁₂ := b₁₂)
    (c₁ := c₁) (c₂ := c₂) (c₁₂ := c₁₂) (L₀ := L₀) (R₀ := R₀) (L₁ := L₁) (R₁ := R₁)
    (L₂ := L₂) (R₂ := R₂) α₁ β₁ α₂ β₂ α₁₂ β₁₂)
    (X : S1836IsoComma L₀ R₀) :
    L₂.map (ca.hom.app X.obj.left) ≫ (α₂.hom.app (a₁.obj X.obj.left) ≫
      c₂.map (α₁.hom.app X.obj.left ≫ c₁.map X.obj.hom ≫ β₁.hom.app X.obj.right) ≫
      β₂.hom.app (b₁.obj X.obj.right)) =
    (α₁₂.hom.app X.obj.left ≫ c₁₂.map X.obj.hom ≫ β₁₂.hom.app X.obj.right) ≫
      R₂.map (cb.hom.app X.obj.right) := by
  have h := sq X.obj.left X.obj.right X.obj.hom
  simpa only [Functor.map_comp, Category.assoc] using h

/-- **The comparison isomorphism between the restriction along a composite and
the composite of the two restrictions.** -/
noncomputable def S1890RestrictCompIso (sq : S1890CompSquare (ca := ca) (cb := cb)
    (a₁ := a₁) (a₂ := a₂) (a₁₂ := a₁₂) (b₁ := b₁) (b₂ := b₂) (b₁₂ := b₁₂)
    (c₁ := c₁) (c₂ := c₂) (c₁₂ := c₁₂) (L₀ := L₀) (R₀ := R₀) (L₁ := L₁) (R₁ := R₁)
    (L₂ := L₂) (R₂ := R₂) α₁ β₁ α₂ β₂ α₁₂ β₁₂) :
    S1864IsoCommaRestrict (L := L₀) (R := R₀) (L' := L₂) (R' := R₂) a₁₂ b₁₂ c₁₂ α₁₂ β₁₂ ≅
      S1864IsoCommaRestrict (L := L₀) (R := R₀) (L' := L₁) (R' := R₁) a₁ b₁ c₁ α₁ β₁ ⋙
        S1864IsoCommaRestrict (L := L₁) (R := R₁) (L' := L₂) (R' := R₂) a₂ b₂ c₂ α₂ β₂ :=
  NatIso.ofComponents
    (fun X =>
      ObjectProperty.isoMk (P := fun Z : Comma L₂ R₂ => IsIso Z.hom)
        (Comma.isoMk
          (X := ((S1864IsoCommaRestrict a₁₂ b₁₂ c₁₂ α₁₂ β₁₂).obj X).obj)
          (Y := (((S1864IsoCommaRestrict a₁ b₁ c₁ α₁ β₁) ⋙
            (S1864IsoCommaRestrict a₂ b₂ c₂ α₂ β₂)).obj X).obj)
          (ca.app X.obj.left) (cb.app X.obj.right) (by
            exact S1890CompSquareAux sq X)))
    (fun {X Y} f => by
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · exact ca.hom.naturality f.hom.left
      · exact cb.hom.naturality f.hom.right)

end RestrictComp

/-! ## 2. The identity restriction comparison -/

section RestrictId

variable {A₀ B₀ C₀ : Type u}
  [Category.{u, u} A₀] [Category.{u, u} B₀] [Category.{u, u} C₀]
  {a₀ : A₀ ⥤ A₀} {ca₀ : a₀ ≅ 𝟭 A₀}
  {b₀ : B₀ ⥤ B₀} {cb₀ : b₀ ≅ 𝟭 B₀}
  {c₀ : C₀ ⥤ C₀}
  {L : A₀ ⥤ C₀} {R : B₀ ⥤ C₀}
  {α₀ : a₀ ⋙ L ≅ L ⋙ c₀} {β₀ : R ⋙ c₀ ≅ b₀ ⋙ R}

/-- The pointwise 2-commuting square for the identity comparison. -/
def S1890IdSquare : Prop :=
  ∀ (x : A₀) (y : B₀) (h : L.obj x ⟶ R.obj y),
    L.map (ca₀.hom.app x) ≫ h = (α₀.hom.app x ≫ c₀.map h ≫ β₀.hom.app y) ≫ R.map (cb₀.hom.app y)

/-- The comma-level square for the identity comparison. -/
theorem S1890IdSquareAux (sq : S1890IdSquare (ca₀ := ca₀) (cb₀ := cb₀)
    (L := L) (R := R) (α₀ := α₀) (β₀ := β₀) (c₀ := c₀)) (X : S1836IsoComma L R) :
    L.map (ca₀.hom.app X.obj.left) ≫ X.obj.hom =
      (α₀.hom.app X.obj.left ≫ c₀.map X.obj.hom ≫ β₀.hom.app X.obj.right) ≫
        R.map (cb₀.hom.app X.obj.right) := by
  have h := sq X.obj.left X.obj.right X.obj.hom
  simpa only [Category.assoc] using h

/-- **The comparison isomorphism between the restriction along an identity and
the identity functor.** -/
noncomputable def S1890RestrictIdIso (sq : S1890IdSquare (ca₀ := ca₀) (cb₀ := cb₀)
    (L := L) (R := R) (α₀ := α₀) (β₀ := β₀) (c₀ := c₀)) :
    S1864IsoCommaRestrict (L := L) (R := R) (L' := L) (R' := R) a₀ b₀ c₀ α₀ β₀ ≅
      𝟭 (S1836IsoComma L R) :=
  NatIso.ofComponents
    (fun X =>
      ObjectProperty.isoMk (P := fun Z : Comma L R => IsIso Z.hom)
        (Comma.isoMk
          (X := ((S1864IsoCommaRestrict a₀ b₀ c₀ α₀ β₀).obj X).obj)
          (Y := X.obj)
          (ca₀.app X.obj.left) (cb₀.app X.obj.right) (by
            exact S1890IdSquareAux sq X)))
    (fun {X Y} f => by
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · exact ca₀.hom.naturality f.hom.left
      · exact cb₀.hom.naturality f.hom.right)

end RestrictId
/-! ## 3. The site-level data and the proven pasting identities -/

section Site

/-- The value of the iso-comma site pseudofunctor at a test object. -/
noncomputable def S1890IsoCommaObj {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :=
  Cat.of (S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor)

/-- The 1-cell of the iso-comma site pseudofunctor at a site morphism. -/
noncomputable def S1890IsoCommaMap {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    S1890IsoCommaObj f g U ⟶ S1890IsoCommaObj f g V :=
  (S1864CoverIsoCommaRestrict f g φ).toCatHom

/-- The site map is strictly compatible with the first iso-comma projection. -/
theorem S1890IsoCommaMap_fst {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    (S1890IsoCommaMap f g φ).toFunctor ⋙
        S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor =
      S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor ⋙
        (A.source.fiber.map φ).toFunctor :=
  rfl

/-- The site map is strictly compatible with the second iso-comma projection. -/
theorem S1890IsoCommaMap_snd {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    (S1890IsoCommaMap f g φ).toFunctor ⋙
        S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor =
      S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor ⋙
        (B.source.fiber.map φ).toFunctor :=
  rfl

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)

/-- The f-side pasting identity: the two stack mapComp comparisons and the
naturality 2-isomorphism of the first cover map.  This is the componentwise
form of `Pseudofunctor.StrongTrans.naturality_comp_hom_app` for `f.map`
after multiplying by the C-comparison; it is stated here exactly and is one of
the two formal steps not closed in this file (the other being
`S1890SiteCompG`). -/
def S1890SiteCompF (x : ↥(A.source.fiber.obj U)) : Prop :=
    (f.map.app W).toFunctor.map
        ((A.source.fiber.mapComp φ ψ).hom.toNatTrans.app x) ≫
      (f.map.naturality ψ).hom.toNatTrans.app ((A.source.fiber.map φ).toFunctor.obj x) ≫
        (C.source.fiber.map ψ).toFunctor.map
          ((f.map.naturality φ).hom.toNatTrans.app x)
    = (f.map.naturality (φ ≫ ψ)).hom.toNatTrans.app x ≫
        (C.source.fiber.mapComp φ ψ).hom.toNatTrans.app
          ((f.map.app U).toFunctor.obj x)


/-- The C-side naturality of the C-comparison at the structure morphism. -/
theorem S1890SiteCompC (x : ↥(A.source.fiber.obj U)) (y : ↥(B.source.fiber.obj U))
    (h : (f.map.app U).toFunctor.obj x ⟶ (g.map.app U).toFunctor.obj y) :
    (C.source.fiber.mapComp φ ψ).hom.toNatTrans.app
        ((f.map.app U).toFunctor.obj x) ≫
      (C.source.fiber.map ψ).toFunctor.map ((C.source.fiber.map φ).toFunctor.map h)
    = (C.source.fiber.map (φ ≫ ψ)).toFunctor.map h ≫
        (C.source.fiber.mapComp φ ψ).hom.toNatTrans.app
          ((g.map.app U).toFunctor.obj y) :=
  (NatTrans.naturality
    (Cat.Hom.toNatIso (C.source.fiber.mapComp φ ψ)).hom h).symm

/-- The g-side pasting identity, in the beta (inverse naturality) direction:
the componentwise form of `naturality_comp_inv_app` for `g.map` after the
cancellation of the B-comparison with its inverse. -/
def S1890SiteCompG (y : ↥(B.source.fiber.obj U)) : Prop :=
    (C.source.fiber.mapComp φ ψ).hom.toNatTrans.app
        ((g.map.app U).toFunctor.obj y) ≫
      (C.source.fiber.map ψ).toFunctor.map
        ((g.map.naturality φ).inv.toNatTrans.app y) ≫
        (g.map.naturality ψ).inv.toNatTrans.app ((B.source.fiber.map φ).toFunctor.obj y)
    = (g.map.naturality (φ ≫ ψ)).inv.toNatTrans.app y ≫
        (g.map.app W).toFunctor.map
          ((B.source.fiber.mapComp φ ψ).hom.toNatTrans.app y)

end Site

/-! ## 4. The exact first missing statements -/

section Missing

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- **The identity g-side pasting identity (m1).**  For every test object U the
identity naturality 2-isomorphism of `g.map` and the `mapId` comparison of
`B.source.fiber` cancel against the structure morphism.  This is the mirror
image of the f-side identity coherence `S1890SiteIdF`; the g-side uses
`naturality_id_inv_app` and the inverse of the `mapId` comparison. -/
def S1890SiteIdG (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) : Prop :=
  ∀ (x : ↥(A.source.fiber.obj U)) (y : ↥(B.source.fiber.obj U))
    (h : (f.map.app U).toFunctor.obj x ⟶ (g.map.app U).toFunctor.obj y),
    (g.map.naturality (𝟙 U)).inv.toNatTrans.app y ≫
        (g.map.app U).toFunctor.map ((B.source.fiber.mapId U).hom.toNatTrans.app y)
      = (C.source.fiber.mapId U).hom.toNatTrans.app ((g.map.app U).toFunctor.obj y)

/-- **The identity square condition (m1 packaged).**  This is exactly the
pointwise square consumed by `S1890RestrictIdIso` when it is applied to the
site data; its f-side half is `S1890SiteIdF`-shaped, its C-side half is the
naturality of the C `mapId` comparison, and its g-side half is
`S1890SiteIdG`. -/
def S1890SiteIdSquare (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) : Prop :=
  ∀ (x : ↥(A.source.fiber.obj U)) (y : ↥(B.source.fiber.obj U))
    (h : (f.map.app U).toFunctor.obj x ⟶ (g.map.app U).toFunctor.obj y),
    (f.map.app U).toFunctor.map ((A.source.fiber.mapId U).hom.toNatTrans.app x) ≫ h =
      ((f.map.naturality (𝟙 U)).hom.toNatTrans.app x ≫
        (C.source.fiber.map (𝟙 U)).toFunctor.map h ≫
          (g.map.naturality (𝟙 U)).inv.toNatTrans.app y) ≫
        (g.map.app U).toFunctor.map ((B.source.fiber.mapId U).hom.toNatTrans.app y)

/-- The identity f-side pasting identity, the f-side half of
`S1890SiteIdSquare`. -/
def S1890SiteIdF (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (x : ↥(A.source.fiber.obj U)) : Prop :=
    (f.map.app U).toFunctor.map ((A.source.fiber.mapId U).hom.toNatTrans.app x)
    = (f.map.naturality (𝟙 U)).hom.toNatTrans.app x ≫
        (C.source.fiber.mapId U).hom.toNatTrans.app ((f.map.app U).toFunctor.obj x)

end Missing
/-! ## 5. The pseudofunctor coherence equations (the next missing, m2) -/

section Coherence

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {U V W Z : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}

/-- **The three pseudofunctor coherence equations (m2), stated for comparison
data of the prescribed components.**  These are verbatim the last three
arguments of `LocallyDiscrete.mkPseudofunctor` for the object assignment
`S1890IsoCommaObj f g` and the 1-cell assignment `S1890IsoCommaMap f g`.
Each equation is true: projecting along `S1836IsoCommaFst` (resp.
`S1836IsoCommaSnd`) reduces it to the corresponding associator/unitor
coherence of `A.source.fiber` (resp. `B.source.fiber`), whose source
2-cells are identities because the etale site is locally discrete.  The
formal projection-level computation is the next missing item. -/
def S1890PseudofunctorCoherence
    (mapComp : ∀ {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
      (φ : U ⟶ V) (ψ : V ⟶ W),
      S1890IsoCommaMap f g (φ ≫ ψ) ≅
        S1890IsoCommaMap f g φ ≫ S1890IsoCommaMap f g ψ)
    (mapId : ∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ),
      S1890IsoCommaMap f g (𝟙 U) ≅ 𝟙 (S1890IsoCommaObj f g U)) : Prop :=
  (∀ {U V W Z : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
      (φ : U ⟶ V) (ψ : V ⟶ W) (χ : W ⟶ Z),
      (mapComp (φ ≫ ψ) χ).hom ≫
        (mapComp φ ψ).hom ▷ S1890IsoCommaMap f g χ ≫
          (α_ (S1890IsoCommaMap f g φ) (S1890IsoCommaMap f g ψ)
            (S1890IsoCommaMap f g χ)).hom ≫
            S1890IsoCommaMap f g φ ◁ (mapComp ψ χ).inv ≫
              (mapComp φ (ψ ≫ χ)).inv = eqToHom (by simp)) ∧
  (∀ {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V),
      (mapComp (𝟙 U) φ).hom ≫ (mapId U).hom ▷ S1890IsoCommaMap f g φ ≫
        (λ_ (S1890IsoCommaMap f g φ)).hom = eqToHom (by simp)) ∧
  (∀ {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V),
      (mapComp φ (𝟙 V)).hom ≫ S1890IsoCommaMap f g φ ◁ (mapId V).hom ≫
        (ρ_ (S1890IsoCommaMap f g φ)).hom = eqToHom (by simp))

end Coherence

/-! ## 6. The exact first missing -/

section FirstMissing

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- **The exact first missing**, relative to candidate comparison data.  It
consists of two parts:
(m1) the identity g-side pasting identity at every test object
     (`S1890SiteIdG`), whose f-side is `S1890SiteIdF` and whose C-side is the
     naturality of the C `mapId` comparison; together they make the identity
     restriction comparison `S1890RestrictIdIso` available at the site;
(m2) the three pseudofunctor coherence equations (`S1890PseudofunctorCoherence`)
     for the comparison data.
The composite comparison square condition is assembled from the three
site-level pasting identities `S1890SiteCompF`, `S1890SiteCompC`,
`S1890SiteCompG`; of these `S1890SiteCompC` is proved in section 3, while
`S1890SiteCompF` and `S1890SiteCompG` are stated there and remain the first
formal steps not closed (they are the componentwise Mathlib `_app`
coherences followed by an `Iso`-inverse cancellation). -/
def S1890FirstMissing
    (mapComp : ∀ {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
      (φ : U ⟶ V) (ψ : V ⟶ W),
      S1890IsoCommaMap f g (φ ≫ ψ) ≅
        S1890IsoCommaMap f g φ ≫ S1890IsoCommaMap f g ψ)
    (mapId : ∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ),
      S1890IsoCommaMap f g (𝟙 U) ≅ 𝟙 (S1890IsoCommaObj f g U)) : Prop :=
  (∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ), S1890SiteIdG f g U) ∧
  S1890PseudofunctorCoherence f g mapComp mapId

end FirstMissing

/-! ## 7. Checks and axiom audit -/

#check S1890CompSquare
#check S1890CompSquareAux
#check S1890RestrictCompIso
#check S1890IdSquare
#check S1890IdSquareAux
#check S1890RestrictIdIso
#check S1890IsoCommaObj
#check S1890IsoCommaMap
#check S1890IsoCommaMap_fst
#check S1890IsoCommaMap_snd
#check S1890SiteCompF
#check S1890SiteCompC
#check S1890SiteCompG
#check S1890SiteIdF
#check S1890SiteIdG
#check S1890SiteIdSquare
#check S1890PseudofunctorCoherence
#check S1890FirstMissing

#print axioms S1890CompSquareAux
#print axioms S1890RestrictCompIso
#print axioms S1890IdSquareAux
#print axioms S1890RestrictIdIso
#print axioms S1890IsoCommaMap_fst
#print axioms S1890IsoCommaMap_snd
#print axioms S1890SiteCompF
#print axioms S1890SiteCompC
#print axioms S1890SiteCompG
#print axioms S1890SiteIdF

end LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual