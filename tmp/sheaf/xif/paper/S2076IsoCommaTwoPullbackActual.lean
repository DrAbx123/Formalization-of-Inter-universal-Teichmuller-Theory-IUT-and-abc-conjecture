import tmp.sheaf.xif.paper.S2074IsoCommaTwoPullbackActual

/-!
# S2076: the iso-comma square is a two-pullback for *every* pseudo-cone

S2074 isolated the last missing input of D6(c), S2058IsoCommaTwoPullback, and
recorded it as S2074IsoCommaTwoPullbackStatement: for every cospan of actual
finite-etale cover maps the square (toA f g, toB f g, f.map, g.map) has the
full EtalePseudofunctorSquare.TwoPullbackWitness.  The tree contained the
fibre-level universal property (S1893Lift, S1893ComparisonFunctor,
S1893LiftUniq) and the site-level lift S1985.liftSite, but the latter only
for the *bicones* S1832Bicone whose two legs are actual cover maps.

This file removes that restriction and proves the statement.

## What is constructed (no sorry, no new axiom, no fabricated 2-cell)

For an arbitrary pseudo-cone c = (W, toA, toB, commutes) over the cospan
(S2074GeneralCone, and the same data with the apex fixed in S2076Cone):

1.  generalLiftNat (gLiftNat): for every site morphism phi : U --> V the
    natural iso
      (W.map phi) ; liftApp V  ~  liftApp U ; (S1890IsoCommaMap f g phi),
    obtained from c.toA.naturality, c.toB.naturality, c.commutes and the
    fibre-level comparison functor S1893ComparisonFunctor
    (gLiftConeIso is the cone-level iso, gLiftNat its preimage under full
    faithfulness).
2.  gLiftSite: the strong transformation W --> sitePseudofunctor f g with
    app U = liftApp U, naturality gLiftNat, and the full
    naturality_naturality, naturality_id, naturality_comp coherence, proved
    from c.toA.naturality_id/_comp, c.toB.naturality_id/_comp and
    siteMapId/siteMapComp (the analogues of S1985's coherence, now for an
    arbitrary cone).
3.  gLiftToA, gLiftToB: the modification isomorphisms with the two legs of the
    square; their components are the strict identities gLiftApp_fst,
    gLiftApp_snd, and their site-level naturality is
    vcomp_gLift_toA_naturality_hom / vcomp_gLift_toB_naturality_hom.
4.  gTwoCellAt, gLiftTwoCell, gLiftTwoCell_toA, gLiftTwoCell_toB: the action
    on cone morphisms.  A morphism of cones m gives, at each U, a morphism of
    the iso-comma fibres (CommaMorphism with left component m.toA and right
    component m.toB, compatible by m.compatibility), hence a 2-cell of lifts;
    the modification naturality is the naturality of m.toA and m.toB, and the
    two projection equations are the strict identity components of
    gLiftToA/gLiftToB.
5.  gTwoCell_ext: joint faithfulness of the two projections, from
    S1836IsoComma_hom_ext.

The witness is assembled as S2076Witness, the statement as
S2076IsoCommaTwoPullback : S2074IsoCommaTwoPullbackStatement, and the exact
D6(c) input as S2076S2058IsoCommaTwoPullback : S2058IsoCommaTwoPullback.

## Axiom footprint

Only propext, Classical.choice and Quot.sound (see the #print axioms block at
the end).  No sorry, no new axiom, no Shrink/ULift/PUnit, and no weakening of
the statement: the cone is arbitrary (W is any category-valued etale
pseudofunctor, the two legs any strong transformations, the 2-cell any iso),
exactly as in S2058/S2074.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual

universe u

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

noncomputable def generalCommutesApp (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp c.toA f.map).app U ≅
      (Pseudofunctor.StrongTrans.vcomp c.toB g.map).app U where
  hom := c.commutes.hom.as.app U
  inv := c.commutes.inv.as.app U
  hom_inv_id := by
    have h := congrArg (fun m => m.as.app U) c.commutes.hom_inv_id
    exact h
  inv_hom_id := by
    have h := congrArg (fun m => m.as.app U) c.commutes.inv_hom_id
    exact h

noncomputable def gConeAt (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor ↥(c.W.obj U) where
  toA := (c.toA.app U).toFunctor
  toB := (c.toB.app U).toFunctor
  commutes := Cat.Hom.toNatIso (generalCommutesApp (f := f) (g := g) c U)

noncomputable def gLiftApp (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    ↑(c.W.obj U) ⥤ S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor :=
  S1893Lift (f.map.app U).toFunctor (g.map.app U).toFunctor (gConeAt (f := f) (g := g) c U)

theorem gLiftApp_fst (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    gLiftApp (f := f) (g := g) c U ⋙
        S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor =
      (c.toA.app U).toFunctor := rfl

theorem gLiftApp_snd (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    gLiftApp (f := f) (g := g) c U ⋙
        S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor =
      (c.toB.app U).toFunctor := rfl

/-! ## 2. Naturality comparisons for the general cone -/

theorem vcomp_toA_naturality_apply (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(c.W.obj U)) :
    ((Pseudofunctor.StrongTrans.vcomp c.toA f.map).naturality φ).hom.toNatTrans.app x =
      (f.map.app V).toFunctor.map ((c.toA.naturality φ).hom.toNatTrans.app x) ≫
        (S1864SiteComparisonLeft f φ).hom.app ((c.toA.app U).toFunctor.obj x) := by
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom,
    Pseudofunctor.StrongTrans.toOplax, S1864SiteComparisonLeft,
    Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
    Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.eqToHom_app,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, eqToIso.hom,
    Category.comp_id, Category.id_comp]
  simp
  erw [Category.id_comp]

theorem vcomp_toB_naturality_apply (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(c.W.obj U)) :
    ((Pseudofunctor.StrongTrans.vcomp c.toB g.map).naturality φ).hom.toNatTrans.app x =
      (g.map.app V).toFunctor.map ((c.toB.naturality φ).hom.toNatTrans.app x) ≫
        (S1864SiteComparisonRight g φ).inv.app ((c.toB.app U).toFunctor.obj x) := by
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom,
    Pseudofunctor.StrongTrans.toOplax, S1864SiteComparisonRight,
    Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
    Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.eqToHom_app,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, eqToIso.hom,
    Category.comp_id, Category.id_comp]
  simp
  erw [Category.id_comp]

noncomputable def gLiftNatConeA (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    (((c.W.map φ).toFunctor ⋙ gLiftApp (f := f) (g := g) c V) ⋙
        S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor) ⟶
      ((gLiftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor) ⋙
        S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor) :=
  (c.toA.naturality φ).hom.toNatTrans

noncomputable def gLiftNatConeB (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    (((c.W.map φ).toFunctor ⋙ gLiftApp (f := f) (g := g) c V) ⋙
        S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor) ⟶
      ((gLiftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor) ⋙
        S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor) :=
  (c.toB.naturality φ).hom.toNatTrans

theorem gCone1_commutes_app (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(c.W.obj U)) :
    ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(c.W.obj U)).obj
          ((c.W.map φ).toFunctor ⋙ gLiftApp (f := f) (g := g) c V)).commutes.hom.app x =
      (c.commutes.hom.as.app V).toNatTrans.app ((c.W.map φ).toFunctor.obj x) := by
  rw [S1893ComparisonFunctor_obj_commutes_hom_app, S1836IsoCommaNatIso_hom_app]
  change ((gLiftApp (f := f) (g := g) c V).obj
    ((c.W.map φ).toFunctor.obj x)).obj.hom = _
  simp only [gLiftApp]
  rw [S1893Lift_structure]
  rfl

theorem gCone2_commutes_app (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(c.W.obj U)) :
    ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(c.W.obj U)).obj
          (gLiftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor)).commutes.hom.app x =
      (S1864SiteComparisonLeft f φ).hom.app ((c.toA.app U).toFunctor.obj x) ≫
        (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x) ≫
          (S1864SiteComparisonRight g φ).hom.app ((c.toB.app U).toFunctor.obj x) := by
  rw [S1893ComparisonFunctor_obj_commutes_hom_app, S1836IsoCommaNatIso_hom_app]
  change ((S1864IsoCommaRestrict (A.source.fiber.map φ).toFunctor
      (B.source.fiber.map φ).toFunctor (C.source.fiber.map φ).toFunctor
      (S1864SiteComparisonLeft f φ) (S1864SiteComparisonRight g φ)).obj
        ((S1893Lift (f.map.app U).toFunctor (g.map.app U).toFunctor
          (gConeAt (f := f) (g := g) c U)).obj x)).obj.hom = _
  rw [S1864IsoCommaRestrict_obj_hom]
  rw [S1893Lift_structure]
  rfl

theorem gLiftCone_compat (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(c.W.obj U)) :
    (f.map.app V).toFunctor.map ((c.toA.naturality φ).hom.toNatTrans.app x) ≫
        ((S1864SiteComparisonLeft f φ).hom.app ((c.toA.app U).toFunctor.obj x) ≫
          (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x) ≫
            (S1864SiteComparisonRight g φ).hom.app ((c.toB.app U).toFunctor.obj x)) =
      (c.commutes.hom.as.app V).toNatTrans.app ((c.W.map φ).toFunctor.obj x) ≫
        (g.map.app V).toFunctor.map ((c.toB.naturality φ).hom.toNatTrans.app x) := by
  have h := congrArg (fun m => m.toNatTrans.app x) (c.commutes.hom.as.naturality φ)
  simp only [Functor.whiskerRight_app, NatTrans.toCatHom₂_toNatTrans,
      Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at h
  rw [vcomp_toA_naturality_apply (f := f) (g := g) c φ x,
      vcomp_toB_naturality_apply (f := f) (g := g) c φ x] at h
  calc
    (f.map.app V).toFunctor.map ((c.toA.naturality φ).hom.toNatTrans.app x) ≫
        ((S1864SiteComparisonLeft f φ).hom.app ((c.toA.app U).toFunctor.obj x) ≫
          (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x) ≫
            (S1864SiteComparisonRight g φ).hom.app ((c.toB.app U).toFunctor.obj x))
        = ((((f.map.app V).toFunctor.map ((c.toA.naturality φ).hom.toNatTrans.app x) ≫
            (S1864SiteComparisonLeft f φ).hom.app ((c.toA.app U).toFunctor.obj x)) ≫
              (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x)) ≫
                (S1864SiteComparisonRight g φ).hom.app ((c.toB.app U).toFunctor.obj x)) := by
          simp only [Category.assoc]
    _ = ((c.commutes.hom.as.app V).toNatTrans.app ((c.W.map φ).toFunctor.obj x) ≫
            ((g.map.app V).toFunctor.map ((c.toB.naturality φ).hom.toNatTrans.app x) ≫
              (S1864SiteComparisonRight g φ).inv.app ((c.toB.app U).toFunctor.obj x))) ≫
                  (S1864SiteComparisonRight g φ).hom.app ((c.toB.app U).toFunctor.obj x) := by
          rw [← h]
    _ = (c.commutes.hom.as.app V).toNatTrans.app ((c.W.map φ).toFunctor.obj x) ≫
          (g.map.app V).toFunctor.map ((c.toB.naturality φ).hom.toNatTrans.app x) := by
          simp only [Category.assoc, Iso.inv_hom_id_app]
          erw [Category.comp_id]

/-! ## 3. The comparison cone hom and the naturality iso -/

noncomputable def gLiftConeHomForward (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    S1893Cone.Hom
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(c.W.obj U)).obj
          ((c.W.map φ).toFunctor ⋙ gLiftApp (f := f) (g := g) c V))
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(c.W.obj U)).obj
          (gLiftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor)) :=
  ⟨(gLiftNatConeA (f := f) (g := g) c φ, gLiftNatConeB (f := f) (g := g) c φ), by
    apply NatTrans.ext
    funext x
    dsimp only
    simp only [NatTrans.comp_app, Functor.whiskerRight_app]
    rw [gCone1_commutes_app, gCone2_commutes_app]
    dsimp only [gLiftNatConeA, gLiftNatConeB]
    exact gLiftCone_compat f g c φ x⟩

theorem coneHom_isIso {A' B' C' X : Type u} [Category.{u, u} A'] [Category.{u, u} B']
    [Category.{u, u} C'] [Category.{u, u} X] {L : A' ⥤ C'} {R : B' ⥤ C'}
    {c₁ c₂ : S1893Cone L R X} (m : S1893Cone.Hom c₁ c₂)
    [IsIso m.toA] [IsIso m.toB] : IsIso (C := S1893Cone L R X) m := by
  let invA : c₂.toA ⟶ c₁.toA := inv m.toA
  let invB : c₂.toB ⟶ c₁.toB := inv m.toB
  have hα : Functor.whiskerRight invA L = inv (Functor.whiskerRight m.toA L) := by
    dsimp [invA]
    simp
  have hβ : Functor.whiskerRight invB R = inv (Functor.whiskerRight m.toB R) := by
    dsimp [invB]
    simp
  have hcomp : Functor.whiskerRight invA L ≫ c₁.commutes.hom =
      c₂.commutes.hom ≫ Functor.whiskerRight invB R := by
    have hm := m.2
    have hf : c₁.commutes.hom = Functor.whiskerRight m.toA L ≫ c₂.commutes.hom ≫
        inv (Functor.whiskerRight m.toB R) := by
      calc
        c₁.commutes.hom = (c₁.commutes.hom ≫ Functor.whiskerRight m.toB R) ≫
            inv (Functor.whiskerRight m.toB R) := by
          rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        _ = (Functor.whiskerRight m.toA L ≫ c₂.commutes.hom) ≫
            inv (Functor.whiskerRight m.toB R) := by rw [← hm]
        _ = Functor.whiskerRight m.toA L ≫ c₂.commutes.hom ≫
            inv (Functor.whiskerRight m.toB R) := by simp only [Category.assoc]
    rw [hα, hβ]
    calc
      inv (Functor.whiskerRight m.toA L) ≫ c₁.commutes.hom =
          inv (Functor.whiskerRight m.toA L) ≫
            (Functor.whiskerRight m.toA L ≫ c₂.commutes.hom ≫
              inv (Functor.whiskerRight m.toB R)) := by rw [hf]
      _ = c₂.commutes.hom ≫ inv (Functor.whiskerRight m.toB R) := by
        simp only [← Category.assoc]
        rw [← hα, ← Functor.whiskerRight_comp]
        rw [show invA ≫ m.toA = 𝟙 c₂.toA by dsimp [invA]; simp]
        rw [Functor.whiskerRight_id']
        simp
  let inv' : S1893Cone.Hom c₂ c₁ := ⟨(invA, invB), hcomp⟩
  refine ⟨inv', ?_, ?_⟩
  · apply S1893Cone.Hom.ext
    · change m.toA ≫ invA = 𝟙 c₁.toA
      dsimp [invA]
      simp
    · change m.toB ≫ invB = 𝟙 c₁.toB
      dsimp [invB]
      simp
  · apply S1893Cone.Hom.ext
    · change invA ≫ m.toA = 𝟙 c₂.toA
      dsimp [invA]
      simp
    · change invB ≫ m.toB = 𝟙 c₂.toB
      dsimp [invB]
      simp

noncomputable def gLiftConeIso (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    Iso
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(c.W.obj U)).obj
          ((c.W.map φ).toFunctor ⋙ gLiftApp (f := f) (g := g) c V))
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(c.W.obj U)).obj
          (gLiftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor)) := by
  haveI hA : IsIso (gLiftConeHomForward (f := f) (g := g) c φ).toA := by
    change IsIso ((c.toA.naturality φ).hom.toNatTrans)
    infer_instance
  haveI hB : IsIso (gLiftConeHomForward (f := f) (g := g) c φ).toB := by
    change IsIso ((c.toB.naturality φ).hom.toNatTrans)
    infer_instance
  letI : IsIso (C := S1893Cone (f.map.app V).toFunctor (g.map.app V).toFunctor
      ↥(c.W.obj U)) (gLiftConeHomForward (f := f) (g := g) c φ) :=
    coneHom_isIso (m := gLiftConeHomForward (f := f) (g := g) c φ)
  exact asIso (gLiftConeHomForward (f := f) (g := g) c φ)

noncomputable def gLiftNat (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    Iso (((c.W.map φ).toFunctor ⋙ gLiftApp (f := f) (g := g) c V))
      (gLiftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor) :=
  Functor.FullyFaithful.preimageIso
    (Functor.FullyFaithful.ofFullyFaithful
      (S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(c.W.obj U)))
    (gLiftConeIso (f := f) (g := g) c φ)

theorem gLiftNat_hom_fst (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    Functor.whiskerRight (gLiftNat (f := f) (g := g) c φ).hom
        (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor) =
      gLiftNatConeA (f := f) (g := g) c φ := by
  change ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
      ↥(c.W.obj U)).map (gLiftNat (f := f) (g := g) c φ).hom).toA =
    gLiftNatConeA (f := f) (g := g) c φ
  dsimp only [gLiftNat]
  simp only [Functor.FullyFaithful.preimageIso, Functor.FullyFaithful.map_preimage]
  rfl

theorem gLiftNat_hom_snd (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    Functor.whiskerRight (gLiftNat (f := f) (g := g) c φ).hom
        (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor) =
      gLiftNatConeB (f := f) (g := g) c φ := by
  change ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
      ↥(c.W.obj U)).map (gLiftNat (f := f) (g := g) c φ).hom).toB =
    gLiftNatConeB (f := f) (g := g) c φ
  dsimp only [gLiftNat]
  simp only [Functor.FullyFaithful.preimageIso, Functor.FullyFaithful.map_preimage]
  rfl

/-! ## 4. The site-level lift for a general cone -/

noncomputable def gLiftSite (c : S2074GeneralCone f g) :
    Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g) where
  app U := (gLiftApp (f := f) (g := g) c U).toCatHom
  naturality {U V} φ := Cat.Hom.isoMk (gLiftNat (f := f) (g := g) c φ)
  naturality_naturality := by
    intro U V φ ψ η
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have heta : η = 𝟙 φ := Subsingleton.elim _ _
    rw [heta, PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    rw [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
  naturality_id := by
    intro U
    apply Cat.Hom₂.ext
    apply (S1893ComparisonFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
      ↥(c.W.obj U)).map_injective
    apply S1893Cone.Hom.ext
    · apply NatTrans.ext
      funext x
      simp only [Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.Hom.isoMk, Cat.Hom.toNatIso,
        NatTrans.toCatHom₂_toNatTrans, CategoryTheory.Functor.toCatHom_toFunctor]
      dsimp only [S1893ComparisonFunctor]
      change (Functor.whiskerRight
          ((gLiftNat f g c (𝟙 U)).hom ≫
            (gLiftApp f g c U).toCatHom.toFunctor.whiskerLeft
              ((sitePseudofunctor f g).mapId U).hom.toNatTrans)
          (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor)).app x =
        (Functor.whiskerRight
          (Functor.whiskerRight (c.W.mapId U).hom.toNatTrans
              (gLiftApp f g c U).toCatHom.toFunctor ≫
            (λ_ (gLiftApp f g c U).toCatHom).hom.toNatTrans ≫
              (ρ_ (gLiftApp f g c U).toCatHom).inv.toNatTrans)
          (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor)).app x
      rw [Functor.whiskerRight_comp, NatTrans.comp_app]
      simp only [gLiftNat_hom_fst]
      rw [Functor.whiskerRight_left]
      rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp, Functor.whiskerRight_twice]
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Cat.associator_hom_app, Cat.associator_inv_app, Cat.leftUnitor_hom_app,
        Cat.rightUnitor_hom_app, Cat.leftUnitor_inv_app, Cat.rightUnitor_inv_app,
        Category.comp_id, Category.id_comp, siteMapId_fst]
      simp only [Functor.associator]
      erw [Category.id_comp]
      simp only [sitePseudofunctor_mapId]
      rw [siteMapId_fst]
      have h := congrArg (fun m => m.toNatTrans.app x) (c.toA.naturality_id U)
      simp only [CategoryTheory.eqToHom_map]
      try erw [Category.id_comp]
      try erw [Category.comp_id]
      try erw [Category.id_comp]
      try erw [Category.comp_id]
      try erw [Category.id_comp]
      try erw [Category.comp_id]
      convert h using 1
      · rfl
      · rfl
      · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app,
          Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, Category.comp_id,
          Category.id_comp, CategoryTheory.eqToHom_map, eqToHom_refl]
        rfl
    · apply NatTrans.ext
      funext x
      simp only [Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.Hom.isoMk, Cat.Hom.toNatIso,
        NatTrans.toCatHom₂_toNatTrans, CategoryTheory.Functor.toCatHom_toFunctor]
      dsimp only [S1893ComparisonFunctor]
      change (Functor.whiskerRight
          ((gLiftNat f g c (𝟙 U)).hom ≫
            (gLiftApp f g c U).toCatHom.toFunctor.whiskerLeft
              ((sitePseudofunctor f g).mapId U).hom.toNatTrans)
          (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor)).app x =
        (Functor.whiskerRight
          (Functor.whiskerRight (c.W.mapId U).hom.toNatTrans
              (gLiftApp f g c U).toCatHom.toFunctor ≫
            (λ_ (gLiftApp f g c U).toCatHom).hom.toNatTrans ≫
              (ρ_ (gLiftApp f g c U).toCatHom).inv.toNatTrans)
          (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor)).app x
      rw [Functor.whiskerRight_comp, NatTrans.comp_app]
      simp only [gLiftNat_hom_snd]
      rw [Functor.whiskerRight_left]
      rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp, Functor.whiskerRight_twice]
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Cat.associator_hom_app, Cat.associator_inv_app, Cat.leftUnitor_hom_app,
        Cat.rightUnitor_hom_app, Cat.leftUnitor_inv_app, Cat.rightUnitor_inv_app,
        Category.comp_id, Category.id_comp, siteMapId_snd]
      simp only [Functor.associator]
      erw [Category.id_comp]
      simp only [sitePseudofunctor_mapId]
      rw [siteMapId_snd]
      have h := congrArg (fun m => m.toNatTrans.app x) (c.toB.naturality_id U)
      simp only [CategoryTheory.eqToHom_map]
      try erw [Category.id_comp]
      try erw [Category.comp_id]
      try erw [Category.id_comp]
      try erw [Category.comp_id]
      try erw [Category.id_comp]
      try erw [Category.comp_id]
      convert h using 1
      · rfl
      · rfl
      · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app,
          Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, Category.comp_id,
          Category.id_comp, CategoryTheory.eqToHom_map, eqToHom_refl]
        rfl

  naturality_comp := by
    intro U V Z φ ψ
    apply Cat.Hom₂.ext
    apply (S1893ComparisonFunctor (f.map.app Z).toFunctor (g.map.app Z).toFunctor
      ↥(c.W.obj U)).map_injective
    apply S1893Cone.Hom.ext
    · apply NatTrans.ext
      funext x
      simp only [Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.Hom.isoMk, Cat.Hom.toNatIso,
        NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor]
      dsimp only [S1893ComparisonFunctor]
      change (Functor.whiskerRight _ (S1836IsoCommaFst (f.map.app Z).toFunctor (g.map.app Z).toFunctor)).app x =
        (Functor.whiskerRight _ (S1836IsoCommaFst (f.map.app Z).toFunctor (g.map.app Z).toFunctor)).app x
      simp only [Functor.whiskerRight_comp, NatTrans.comp_app,
        Functor.whiskerRight_left, Functor.whiskerRight_twice,
        gLiftNat_hom_fst, sitePseudofunctor_mapComp, siteMapComp_fst,
        sitePseudofunctor_map, S1890IsoCommaMap_fst,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Cat.associator_hom_app, Cat.associator_inv_app,
        Category.comp_id, Category.id_comp, Functor.associator]
      repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
      have hlast : ((S1890IsoCommaMap f g ψ).toFunctor ⋙
          S1836IsoCommaFst (f.map.app Z).toFunctor (g.map.app Z).toFunctor).map
            ((gLiftNat f g c φ).hom.app x) =
          (A.source.fiber.map ψ).toFunctor.map ((gLiftNatConeA f g c φ).app x) := by
        change (A.source.fiber.map ψ).toFunctor.map
            ((Functor.whiskerRight (gLiftNat f g c φ).hom
              (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor)).app x) = _
        rw [gLiftNat_hom_fst]
      rw [hlast]
      have h := congrArg (fun m => m.toNatTrans.app x) (c.toA.naturality_comp φ ψ)
      convert h using 1
      · rfl
      · rfl
      · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
          Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, Cat.associator_hom_app,
          Cat.associator_inv_app, Category.comp_id, Category.id_comp,
          CategoryTheory.eqToHom_map, eqToHom_refl]
        rfl
    · apply NatTrans.ext
      funext x
      simp only [Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.Hom.isoMk, Cat.Hom.toNatIso,
        NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor]
      dsimp only [S1893ComparisonFunctor]
      change (Functor.whiskerRight _ (S1836IsoCommaSnd (f.map.app Z).toFunctor (g.map.app Z).toFunctor)).app x =
        (Functor.whiskerRight _ (S1836IsoCommaSnd (f.map.app Z).toFunctor (g.map.app Z).toFunctor)).app x
      simp only [Functor.whiskerRight_comp, NatTrans.comp_app,
        Functor.whiskerRight_left, Functor.whiskerRight_twice,
        gLiftNat_hom_snd, sitePseudofunctor_mapComp, siteMapComp_snd,
        sitePseudofunctor_map, S1890IsoCommaMap_snd,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Cat.associator_hom_app, Cat.associator_inv_app,
        Category.comp_id, Category.id_comp, Functor.associator]
      repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
      have hlast : ((S1890IsoCommaMap f g ψ).toFunctor ⋙
          S1836IsoCommaSnd (f.map.app Z).toFunctor (g.map.app Z).toFunctor).map
            ((gLiftNat f g c φ).hom.app x) =
          (B.source.fiber.map ψ).toFunctor.map ((gLiftNatConeB f g c φ).app x) := by
        change (B.source.fiber.map ψ).toFunctor.map
            ((Functor.whiskerRight (gLiftNat f g c φ).hom
              (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor)).app x) = _
        rw [gLiftNat_hom_snd]
      rw [hlast]
      have h := congrArg (fun m => m.toNatTrans.app x) (c.toB.naturality_comp φ ψ)
      convert h using 1
      · rfl
      · rfl
      · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
          Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, Cat.associator_hom_app,
          Cat.associator_inv_app, Category.comp_id, Category.id_comp,
          CategoryTheory.eqToHom_map, eqToHom_refl]
        rfl

/-! ## 5. The projection comparisons liftToA / liftToB -/

theorem vcomp_gLift_toA_naturality_hom (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    ((Pseudofunctor.StrongTrans.vcomp (gLiftSite (f := f) (g := g) c) (toA f g)).naturality φ).hom =
      (c.toA.naturality φ).hom := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom,
    Pseudofunctor.StrongTrans.toOplax, toA,
    Cat.Hom.toNatIso, Cat.Hom.isoMk, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
    Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.eqToHom_app,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, eqToIso.hom,
    Category.comp_id, Category.id_comp]
  simp only [gLiftSite, Cat.Hom.isoMk, Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
    Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.eqToHom_app,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, eqToIso.hom,
    Category.comp_id, Category.id_comp]
  rw [← Functor.whiskerRight_app]
  simp only [gLiftNat_hom_fst, gLiftNatConeA, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  erw [Category.id_comp, Category.comp_id]
  change (Functor.whiskerRight (gLiftNat f g c φ).hom
      (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor)).app x =
    (c.toA.naturality φ).hom.toNatTrans.app x
  rw [gLiftNat_hom_fst]
  rfl

theorem vcomp_gLift_toB_naturality_hom (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    ((Pseudofunctor.StrongTrans.vcomp (gLiftSite (f := f) (g := g) c) (toB f g)).naturality φ).hom =
      (c.toB.naturality φ).hom := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom,
    Pseudofunctor.StrongTrans.toOplax, toB,
    Cat.Hom.toNatIso, Cat.Hom.isoMk, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
    Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.eqToHom_app,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, eqToIso.hom,
    Category.comp_id, Category.id_comp]
  simp only [gLiftSite, Cat.Hom.isoMk, Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
    Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.eqToHom_app,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, eqToIso.hom,
    Category.comp_id, Category.id_comp]
  rw [← Functor.whiskerRight_app]
  simp only [gLiftNat_hom_snd, gLiftNatConeA, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  erw [Category.id_comp, Category.comp_id]
  change (Functor.whiskerRight (gLiftNat f g c φ).hom
      (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor)).app x =
    (c.toB.naturality φ).hom.toNatTrans.app x
  rw [gLiftNat_hom_snd]
  rfl

noncomputable def gLiftToA_app (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp (gLiftSite (f := f) (g := g) c) (toA f g)).app U ≅
      c.toA.app U :=
  eqToIso (CategoryTheory.Cat.ext (by
    change (gLiftApp (f := f) (g := g) c U ⋙
      S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor) =
        (c.toA.app U).toFunctor
    exact gLiftApp_fst (f := f) (g := g) c U))

noncomputable def gLiftToA (c : S2074GeneralCone f g) :
    Iso (Pseudofunctor.StrongTrans.vcomp (gLiftSite (f := f) (g := g) c) (toA f g)) c.toA :=
  Pseudofunctor.StrongTrans.isoMk (fun U => gLiftToA_app (f := f) (g := g) c U) (by
    intro U V φ
    simp only [gLiftToA_app, eqToIso.hom, Cat.Hom₂.eqToHom_toNatTrans,
      Bicategory.whiskerLeft_eqToHom, Bicategory.eqToHom_whiskerRight,
      Cat.eqToHom_app, CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map,
      eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp,
      whiskerLeft_id, id_whiskerRight]
    rw [vcomp_gLift_toA_naturality_hom (f := f) (g := g) c φ])

noncomputable def gLiftToB_app (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp (gLiftSite (f := f) (g := g) c) (toB f g)).app U ≅
      c.toB.app U :=
  eqToIso (CategoryTheory.Cat.ext (by
    change (gLiftApp (f := f) (g := g) c U ⋙
      S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor) =
        (c.toB.app U).toFunctor
    exact gLiftApp_snd (f := f) (g := g) c U))

noncomputable def gLiftToB (c : S2074GeneralCone f g) :
    Iso (Pseudofunctor.StrongTrans.vcomp (gLiftSite (f := f) (g := g) c) (toB f g)) c.toB :=
  Pseudofunctor.StrongTrans.isoMk (fun U => gLiftToB_app (f := f) (g := g) c U) (by
    intro U V φ
    simp only [gLiftToB_app, eqToIso.hom, Cat.Hom₂.eqToHom_toNatTrans,
      Bicategory.whiskerLeft_eqToHom, Bicategory.eqToHom_whiskerRight,
      Cat.eqToHom_app, CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map,
      eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp,
      whiskerLeft_id, id_whiskerRight]
    rw [vcomp_gLift_toB_naturality_hom (f := f) (g := g) c φ])

/-! ## 6. Cones with a fixed apex and their morphisms -/

/-- A pseudo-cone over the cospan with a fixed apex pseudofunctor. -/
structure S2076Cone {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (W : EtaleStackPseudofunctor S1726K) where
  toA : Pseudofunctor.StrongTrans W A.source.fiber
  toB : Pseudofunctor.StrongTrans W B.source.fiber
  commutes : Iso (Pseudofunctor.StrongTrans.vcomp toA f.map)
    (Pseudofunctor.StrongTrans.vcomp toB g.map)

/-- A morphism of pseudo-cones with a fixed apex. -/
structure S2076ConeMorphism {A B C : S1728Cover} {f : S1728CoverMap A C}
    {g : S1728CoverMap B C} {W : EtaleStackPseudofunctor S1726K}
    (s t : S2076Cone f g W) where
  toA : s.toA ⟶ t.toA
  toB : s.toB ⟶ t.toB
  compatibility :
    Pseudofunctor.StrongTrans.whiskerRight toA f.map ≫ t.commutes.hom =
      s.commutes.hom ≫ Pseudofunctor.StrongTrans.whiskerRight toB g.map

noncomputable def S2076Cone.toGeneral {A B C : S1728Cover} {f : S1728CoverMap A C}
    {g : S1728CoverMap B C} {W : EtaleStackPseudofunctor S1726K}
    (c : S2076Cone f g W) : S2074GeneralCone f g :=
  ⟨W, c.toA, c.toB, c.commutes⟩

theorem gConeAt_commutes_hom_app (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(c.W.obj U)) :
    ((gConeAt (f := f) (g := g) c U).commutes.app x).hom =
      (c.commutes.hom.as.app U).toNatTrans.app x := rfl

noncomputable def gTwoCellAt {W : EtaleStackPseudofunctor S1726K}
    (s t : S2076Cone f g W) (m : S2076ConeMorphism s t)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    gLiftApp (f := f) (g := g) s.toGeneral U ⟶
      gLiftApp (f := f) (g := g) t.toGeneral U where
  app x :=
    ObjectProperty.homMk
      (P := fun Y : Comma (f.map.app U).toFunctor (g.map.app U).toFunctor => IsIso Y.hom)
      (CommaMorphism.mk ((m.toA.as.app U).toNatTrans.app x)
        ((m.toB.as.app U).toNatTrans.app x) (by
        have h3 := congrArg (fun al => al.toNatTrans.app x)
          (congrArg (fun mm => mm.as.app U) m.compatibility)
        exact h3))
  naturality := by
    intro x y f_1
    apply S1836IsoComma_hom_ext (f.map.app U).toFunctor (g.map.app U).toFunctor
    · simp only [Functor.map_comp, gLiftApp_fst]
      exact (m.toA.as.app U).toNatTrans.naturality f_1
    · simp only [Functor.map_comp, gLiftApp_snd]
      exact (m.toB.as.app U).toNatTrans.naturality f_1

theorem gTwoCellAt_fst {W : EtaleStackPseudofunctor S1726K}
    (s t : S2076Cone f g W) (m : S2076ConeMorphism s t)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    Functor.whiskerRight (gTwoCellAt (f := f) (g := g) s t m U)
        (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor) =
      (m.toA.as.app U).toNatTrans := rfl

theorem gTwoCellAt_snd {W : EtaleStackPseudofunctor S1726K}
    (s t : S2076Cone f g W) (m : S2076ConeMorphism s t)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    Functor.whiskerRight (gTwoCellAt (f := f) (g := g) s t m U)
        (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor) =
      (m.toB.as.app U).toNatTrans := rfl

theorem gTwoCellAt_fst_app {W : EtaleStackPseudofunctor S1726K}
    (s t : S2076Cone f g W) (m : S2076ConeMorphism s t)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (y : ↑(W.obj U)) :
    (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map
        ((gTwoCellAt (f := f) (g := g) s t m U).app y) =
      (m.toA.as.app U).toNatTrans.app y := rfl

theorem gTwoCellAt_snd_app {W : EtaleStackPseudofunctor S1726K}
    (s t : S2076Cone f g W) (m : S2076ConeMorphism s t)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (y : ↑(W.obj U)) :
    (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map
        ((gTwoCellAt (f := f) (g := g) s t m U).app y) =
      (m.toB.as.app U).toNatTrans.app y := rfl

/-- The 2-cell of lifts induced by a morphism of cones. -/
noncomputable def gLiftTwoCell {W : EtaleStackPseudofunctor S1726K}
    (s t : S2076Cone f g W) (m : S2076ConeMorphism s t) :
    gLiftSite (f := f) (g := g) s.toGeneral ⟶
      gLiftSite (f := f) (g := g) t.toGeneral where
  as :=
    { app := fun U => NatTrans.toCatHom₂ (gTwoCellAt (f := f) (g := g) s t m U)
      naturality := by
        intro U V φ
        apply Cat.Hom₂.ext
        apply NatTrans.ext
        funext x
        apply S1836IsoComma_hom_ext (f.map.app V).toFunctor (g.map.app V).toFunctor
        · have hA := congrArg (fun al => al.toNatTrans.app x) (m.toA.as.naturality φ)
          simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
            Functor.whiskerLeft_app, Functor.whiskerRight_app] at hA
          simp only [NatTrans.comp_app, Functor.map_comp, Cat.Hom₂.comp_app,
            Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
            Functor.whiskerLeft_app, Functor.whiskerRight_app, gLiftSite,
            sitePseudofunctor_map, NatTrans.toCatHom₂_toNatTrans, Cat.Hom.isoMk,
            Iso.app_hom]
          rw [gTwoCellAt_fst_app, ← Functor.whiskerRight_app, gLiftNat_hom_fst,
            ← Functor.whiskerRight_app, gLiftNat_hom_fst]
          have hlast :
              (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
                ((S1890IsoCommaMap f g φ).toFunctor.map
                  ((gTwoCellAt (f := f) (g := g) s t m U).app x)) =
                (A.source.fiber.map φ).toFunctor.map
                  ((m.toA.as.app U).toNatTrans.app x) := rfl
          rw [hlast]
          exact hA
        · have hB := congrArg (fun al => al.toNatTrans.app x) (m.toB.as.naturality φ)
          simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
            Functor.whiskerLeft_app, Functor.whiskerRight_app] at hB
          simp only [NatTrans.comp_app, Functor.map_comp, Cat.Hom₂.comp_app,
            Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
            Functor.whiskerLeft_app, Functor.whiskerRight_app, gLiftSite,
            sitePseudofunctor_map, NatTrans.toCatHom₂_toNatTrans, Cat.Hom.isoMk,
            Iso.app_hom]
          rw [gTwoCellAt_snd_app, ← Functor.whiskerRight_app, gLiftNat_hom_snd,
            ← Functor.whiskerRight_app, gLiftNat_hom_snd]
          have hlast :
              (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
                ((S1890IsoCommaMap f g φ).toFunctor.map
                  ((gTwoCellAt (f := f) (g := g) s t m U).app x)) =
                (B.source.fiber.map φ).toFunctor.map
                  ((m.toB.as.app U).toNatTrans.app x) := rfl
          rw [hlast]
          exact hB }

theorem vcomp_gLiftSite_toA_obj (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(c.W.obj U)) :
    ((Pseudofunctor.StrongTrans.vcomp (gLiftSite (f := f) (g := g) c) (toA f g)).app U).toFunctor.obj x =
      (c.toA.app U).toFunctor.obj x := rfl

theorem vcomp_gLiftSite_toB_obj (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(c.W.obj U)) :
    ((Pseudofunctor.StrongTrans.vcomp (gLiftSite (f := f) (g := g) c) (toB f g)).app U).toFunctor.obj x =
      (c.toB.app U).toFunctor.obj x := rfl

@[simp] theorem gLiftToA_hom_app_as (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    ((gLiftToA (f := f) (g := g) c).hom.as.app U).toNatTrans = 𝟙 _ := rfl

@[simp] theorem gLiftToA_inv_app_as (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    ((gLiftToA (f := f) (g := g) c).inv.as.app U).toNatTrans = 𝟙 _ := rfl

@[simp] theorem gLiftToB_hom_app_as (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    ((gLiftToB (f := f) (g := g) c).hom.as.app U).toNatTrans = 𝟙 _ := rfl

@[simp] theorem gLiftToB_inv_app_as (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    ((gLiftToB (f := f) (g := g) c).inv.as.app U).toNatTrans = 𝟙 _ := rfl

theorem gLiftTwoCell_toA {W : EtaleStackPseudofunctor S1726K}
    (s t : S2076Cone f g W) (m : S2076ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight (gLiftTwoCell (f := f) (g := g) s t m)
        (toA f g) =
      (gLiftToA (f := f) (g := g) s.toGeneral).hom ≫ m.toA ≫
        (gLiftToA (f := f) (g := g) t.toGeneral).inv := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext U
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  have hL : ((Pseudofunctor.StrongTrans.whiskerRight (gLiftTwoCell (f := f) (g := g) s t m)
      (toA f g)).as.app U).toNatTrans.app x = (m.toA.as.app U).toNatTrans.app x := rfl
  have hR : (((gLiftToA (f := f) (g := g) s.toGeneral).hom ≫ m.toA ≫
      (gLiftToA (f := f) (g := g) t.toGeneral).inv).as.app U).toNatTrans.app x =
      (m.toA.as.app U).toNatTrans.app x := by
    show ((gLiftToA (f := f) (g := g) s.toGeneral).hom.as.app U).toNatTrans.app x ≫
        (m.toA.as.app U).toNatTrans.app x ≫
        ((gLiftToA (f := f) (g := g) t.toGeneral).inv.as.app U).toNatTrans.app x =
      (m.toA.as.app U).toNatTrans.app x
    simp only [gLiftToA_hom_app_as, gLiftToA_inv_app_as, NatTrans.id_app,
      vcomp_gLiftSite_toA_obj]
    dsimp only [S2076Cone.toGeneral]
    simp only [Category.id_comp, Category.comp_id]
  rw [hL, hR]

theorem gLiftTwoCell_toB {W : EtaleStackPseudofunctor S1726K}
    (s t : S2076Cone f g W) (m : S2076ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight (gLiftTwoCell (f := f) (g := g) s t m)
        (toB f g) =
      (gLiftToB (f := f) (g := g) s.toGeneral).hom ≫ m.toB ≫
        (gLiftToB (f := f) (g := g) t.toGeneral).inv := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext U
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  have hL : ((Pseudofunctor.StrongTrans.whiskerRight (gLiftTwoCell (f := f) (g := g) s t m)
      (toB f g)).as.app U).toNatTrans.app x = (m.toB.as.app U).toNatTrans.app x := rfl
  have hR : (((gLiftToB (f := f) (g := g) s.toGeneral).hom ≫ m.toB ≫
      (gLiftToB (f := f) (g := g) t.toGeneral).inv).as.app U).toNatTrans.app x =
      (m.toB.as.app U).toNatTrans.app x := by
    show ((gLiftToB (f := f) (g := g) s.toGeneral).hom.as.app U).toNatTrans.app x ≫
        (m.toB.as.app U).toNatTrans.app x ≫
        ((gLiftToB (f := f) (g := g) t.toGeneral).inv.as.app U).toNatTrans.app x =
      (m.toB.as.app U).toNatTrans.app x
    simp only [gLiftToB_hom_app_as, gLiftToB_inv_app_as, NatTrans.id_app,
      vcomp_gLiftSite_toB_obj]
    dsimp only [S2076Cone.toGeneral]
    simp only [Category.id_comp, Category.comp_id]
  rw [hL, hR]

theorem gTwoCell_ext {W : EtaleStackPseudofunctor S1726K}
    {first second : Pseudofunctor.StrongTrans W (sitePseudofunctor f g)}
    (alpha beta : first ⟶ second)
    (h1 : Pseudofunctor.StrongTrans.whiskerRight alpha (toA f g) =
      Pseudofunctor.StrongTrans.whiskerRight beta (toA f g))
    (h2 : Pseudofunctor.StrongTrans.whiskerRight alpha (toB f g) =
      Pseudofunctor.StrongTrans.whiskerRight beta (toB f g)) :
    alpha = beta := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext U
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  apply S1836IsoComma_hom_ext (f.map.app U).toFunctor (g.map.app U).toFunctor
  · change ((toA f g).app U).toFunctor.map ((alpha.as.app U).toNatTrans.app x) =
      ((toA f g).app U).toFunctor.map ((beta.as.app U).toNatTrans.app x)
    have h := congrArg (fun al => al.toNatTrans.app x)
      (congrArg (fun mm => mm.as.app U) h1)
    simpa only [Pseudofunctor.StrongTrans.whiskerRight, Cat.whiskerRight_toNatTrans,
      Functor.whiskerRight_app] using h
  · change ((toB f g).app U).toFunctor.map ((alpha.as.app U).toNatTrans.app x) =
      ((toB f g).app U).toFunctor.map ((beta.as.app U).toNatTrans.app x)
    have h := congrArg (fun al => al.toNatTrans.app x)
      (congrArg (fun mm => mm.as.app U) h2)
    simpa only [Pseudofunctor.StrongTrans.whiskerRight, Cat.whiskerRight_toNatTrans,
      Functor.whiskerRight_app] using h

/-! ## 9. The witness of the two-pullback square and the statement -/

/-- The square of the iso-comma projections. -/
noncomputable def S2076Square :
    EtalePseudofunctorSquare (sitePseudofunctor f g) A.source.fiber B.source.fiber
      C.source.fiber :=
  EtalePseudofunctorSquare.mk (toA f g) (toB f g) f.map g.map (commutes f g)

noncomputable def S2076ConeToGeneral {W : EtaleStackPseudofunctor S1726K}
    (c : S2076Square (f := f) (g := g) |>.Cone W) : S2074GeneralCone f g :=
  ⟨W, c.toX, c.toY, c.commutes⟩

noncomputable def S2076ConeToCone {W : EtaleStackPseudofunctor S1726K}
    (c : S2076Square (f := f) (g := g) |>.Cone W) : S2076Cone f g W :=
  ⟨c.toX, c.toY, c.commutes⟩

noncomputable def S2076ConeMorphismTo {W : EtaleStackPseudofunctor S1726K}
    {s t : S2076Square (f := f) (g := g) |>.Cone W}
    (m : S2076Square (f := f) (g := g) |>.ConeMorphism s t) :
    S2076ConeMorphism (S2076ConeToCone (f := f) (g := g) s)
      (S2076ConeToCone (f := f) (g := g) t) :=
  ⟨m.toX, m.toY, m.compatibility⟩

/-- **The two-pullback witness of the iso-comma square for every cospan of actual
cover maps.** -/
noncomputable def S2076Witness :
    (EtalePseudofunctorSquare.mk (toA f g) (toB f g) f.map g.map (commutes f g)).TwoPullbackWitness where
  lift W cone := gLiftSite (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) cone)
  liftToX W cone := gLiftToA (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) cone)
  liftToY W cone := gLiftToB (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) cone)
  liftTwoCell W s t m :=
    gLiftTwoCell (f := f) (g := g) (S2076ConeToCone (f := f) (g := g) s)
      (S2076ConeToCone (f := f) (g := g) t) (S2076ConeMorphismTo (f := f) (g := g) m)
  liftTwoCell_toX W s t m :=
    gLiftTwoCell_toA (f := f) (g := g) (S2076ConeToCone (f := f) (g := g) s)
      (S2076ConeToCone (f := f) (g := g) t) (S2076ConeMorphismTo (f := f) (g := g) m)
  liftTwoCell_toY W s t m :=
    gLiftTwoCell_toB (f := f) (g := g) (S2076ConeToCone (f := f) (g := g) s)
      (S2076ConeToCone (f := f) (g := g) t) (S2076ConeMorphismTo (f := f) (g := g) m)
  twoCell_ext W first second alpha beta h1 h2 :=
    gTwoCell_ext (f := f) (g := g) alpha beta h1 h2

/-- **S2074's exact statement**: the iso-comma square has the full 2-universal
property for every cospan of actual finite-etale cover maps. -/
noncomputable def S2076IsoCommaTwoPullback : S2074IsoCommaTwoPullbackStatement :=
  fun A B C f g => S2076Witness (f := f) (g := g)

/-- **S2058IsoCommaTwoPullback is proved**: the last missing input of D6(c). -/
noncomputable def S2076S2058IsoCommaTwoPullback :
    LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual.S2058IsoCommaTwoPullback :=
  S2076IsoCommaTwoPullback

#check S2076Witness
#check S2074IsoCommaTwoPullbackStatement
#check S2076IsoCommaTwoPullback
#check S2076S2058IsoCommaTwoPullback

#print axioms S2076Witness
#print axioms S2076IsoCommaTwoPullback
#print axioms S2076S2058IsoCommaTwoPullback
#print axioms gLiftSite
#print axioms gLiftTwoCell
#print axioms gTwoCell_ext

end LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual