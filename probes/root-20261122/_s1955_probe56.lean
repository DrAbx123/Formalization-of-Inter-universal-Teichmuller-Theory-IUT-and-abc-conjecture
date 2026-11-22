import tmp.sheaf.xif.paper.S1945SitePseudofunctorDataActual
import tmp.sheaf.xif.paper.S1893PullbackUniversalActual
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
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
set_option linter.unusedSimpArgs false
namespace Probe
variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
noncomputable def toA : Pseudofunctor.StrongTrans (sitePseudofunctor f g) A.source.fiber where
  app U := (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).toCatHom
  naturality {U V} φ := eqToIso rfl
  naturality_naturality := by
    intro a b f_1 g_1 eta
    obtain rfl := LocallyDiscrete.eq_of_hom eta
    have heta : eta = 𝟙 f_1 := Subsingleton.elim _ _
    rw [heta, PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    rw [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
  naturality_id := by
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
      Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app, Category.comp_id, Category.id_comp]
    simp only [CategoryTheory.Functor.toCatHom_toFunctor, sitePseudofunctor_mapId]
    simp
    change (A.source.fiber.mapId a).hom.toNatTrans.app X.obj.left =
      (S1836IsoCommaFst (f.map.app a).toFunctor (g.map.app a).toFunctor).map
        ((siteMapId f g).hom.toNatTrans.app X)
    rw [siteMapId_fst]
  naturality_comp := by
    intro a b c f_1 g_1
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_app, Cat.associator_inv_app,
      Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
      Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
      Category.comp_id, Category.id_comp]
    simp only [CategoryTheory.Functor.toCatHom_toFunctor, sitePseudofunctor_mapComp]
    simp
    erw [Category.comp_id, Category.comp_id]
    exact (siteMapComp_fst f g f_1 g_1 X).symm

noncomputable def toB : Pseudofunctor.StrongTrans (sitePseudofunctor f g) B.source.fiber where
  app U := (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).toCatHom
  naturality {U V} φ := eqToIso rfl
  naturality_naturality := by
    intro a b f_1 g_1 eta
    obtain rfl := LocallyDiscrete.eq_of_hom eta
    have heta : eta = 𝟙 f_1 := Subsingleton.elim _ _
    rw [heta, PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    rw [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
  naturality_id := by
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
      Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app, Category.comp_id, Category.id_comp]
    simp only [CategoryTheory.Functor.toCatHom_toFunctor, sitePseudofunctor_mapId]
    simp
    change (B.source.fiber.mapId a).hom.toNatTrans.app X.obj.right =
      (S1836IsoCommaSnd (f.map.app a).toFunctor (g.map.app a).toFunctor).map
        ((siteMapId f g).hom.toNatTrans.app X)
    rw [siteMapId_snd]
  naturality_comp := by
    intro a b c f_1 g_1
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_app, Cat.associator_inv_app,
      Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
      Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
      Category.comp_id, Category.id_comp]
    simp only [CategoryTheory.Functor.toCatHom_toFunctor, sitePseudofunctor_mapComp]
    simp
    erw [Category.comp_id, Category.comp_id]
    exact (siteMapComp_snd f g f_1 g_1 X).symm


theorem vcompToA_naturality_apply {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(S1890IsoCommaObj f g U)) :
    (((Pseudofunctor.StrongTrans.vcomp (toA f g) f.map).naturality φ).hom.toNatTrans.app x)
      = (S1864SiteComparisonLeft f φ).hom.app x.obj.left := by
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom,
    Pseudofunctor.StrongTrans.toOplax, toA, S1864SiteComparisonLeft,
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
  erw [Category.id_comp, Category.id_comp]
  trace_state
  change (f.map.naturality φ).hom.toNatTrans.app x.obj.left =
    (f.map.naturality φ).hom.toNatTrans.app x.obj.left
  rfl


theorem vcompToB_naturality_apply {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(S1890IsoCommaObj f g U)) :
    (((Pseudofunctor.StrongTrans.vcomp (toB f g) g.map).naturality φ).hom.toNatTrans.app x)
      = (S1864SiteComparisonRight g φ).inv.app x.obj.right := by
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom,
    Pseudofunctor.StrongTrans.toOplax, toB, S1864SiteComparisonRight,
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
  erw [Category.id_comp, Category.id_comp]
  change (g.map.naturality φ).hom.toNatTrans.app x.obj.right =
    (g.map.naturality φ).hom.toNatTrans.app x.obj.right
  rfl

-- commutes app
noncomputable def commutesApp (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp (toA f g) f.map).app U ≅
      (Pseudofunctor.StrongTrans.vcomp (toB f g) g.map).app U :=
  Cat.Hom.isoMk (S1836IsoCommaNatIso (f.map.app U).toFunctor (g.map.app U).toFunctor)


noncomputable def commutes :
    Iso (Pseudofunctor.StrongTrans.vcomp (toA f g) f.map)
      (Pseudofunctor.StrongTrans.vcomp (toB f g) g.map) :=
  Pseudofunctor.StrongTrans.isoMk (fun U => commutesApp f g U) (by
    intro U V φ
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    simp only [CategoryTheory.Oplax.StrongTrans.vcomp_naturality_hom,
      Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_app, Cat.associator_inv_app]
    simp only [commutesApp, Cat.Hom.isoMk, Cat.Hom.toNatIso, Cat.Hom₂.toNatTrans,
      NatTrans.toCatHom₂_toNatTrans, S1836IsoCommaNatIso_hom_app,
      S1864SiteComparisonLeft, S1864SiteComparisonRight, S1864CoverIsoCommaRestrict]
    change ((S1864IsoCommaRestrict (A.source.fiber.map φ).toFunctor
        (B.source.fiber.map φ).toFunctor (C.source.fiber.map φ).toFunctor
        (S1864SiteComparisonLeft f φ) (S1864SiteComparisonRight g φ)).obj x).obj.hom ≫
        (((toB f g).vcomp g.map).naturality φ).hom.toNatTrans.app x =
      (((toA f g).vcomp f.map).naturality φ).hom.toNatTrans.app x ≫
        (C.source.fiber.map φ).toFunctor.map x.obj.hom
    rw [S1864IsoCommaRestrict_obj_hom]
    rw [vcompToA_naturality_apply, vcompToB_naturality_apply]
    simp only [Iso.app_hom, Iso.app_inv, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
    erw [Category.comp_id])

noncomputable def biconeCommutesApp {W : S1728Cover} (c : S1832Bicone f g W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp c.toA.map f.map).app U ≅
      (Pseudofunctor.StrongTrans.vcomp c.toB.map g.map).app U where
  hom := c.commutes.hom.as.app U
  inv := c.commutes.inv.as.app U
  hom_inv_id := by
    have h := congrArg (fun m => m.as.app U) c.commutes.hom_inv_id
    exact h
  inv_hom_id := by
    have h := congrArg (fun m => m.as.app U) c.commutes.inv_hom_id
    exact h

noncomputable def coneAt {W : S1728Cover} (c : S1832Bicone f g W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor ↥(W.source.fiber.obj U) where
  toA := (c.toA.map.app U).toFunctor
  toB := (c.toB.map.app U).toFunctor
  commutes := Cat.Hom.toNatIso (biconeCommutesApp (f := f) (g := g) c U)

noncomputable def liftApp {W : S1728Cover} (c : S1832Bicone f g W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    ↑(W.source.fiber.obj U) ⥤ S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor :=
  S1893Lift (f.map.app U).toFunctor (g.map.app U).toFunctor (coneAt (f := f) (g := g) c U)


noncomputable def liftConeHomForward {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    S1893Cone.Hom
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)).obj ((W.source.fiber.map φ).toFunctor ⋙ liftApp (f := f) (g := g) c V))
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)).obj
        (liftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor)) := by
  refine ⟨((c.toA.map).naturality φ).hom, ((c.toB.map).naturality φ).hom, ?_⟩
  trace_state
  sorry

end Probe