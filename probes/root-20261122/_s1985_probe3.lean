import tmp.sheaf.xif.paper.S1955AssembleCDActual

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
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1985Probe

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

theorem vcomp_toA_naturality_apply {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(W.source.fiber.obj U)) :
    ((Pseudofunctor.StrongTrans.vcomp c.toA.map f.map).naturality φ).hom.toNatTrans.app x =
      (f.map.app V).toFunctor.map ((c.toA.map.naturality φ).hom.toNatTrans.app x) ≫
        (S1864SiteComparisonLeft f φ).hom.app ((c.toA.map.app U).toFunctor.obj x) := by
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

theorem vcomp_toB_naturality_apply {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(W.source.fiber.obj U)) :
    ((Pseudofunctor.StrongTrans.vcomp c.toB.map g.map).naturality φ).hom.toNatTrans.app x =
      (g.map.app V).toFunctor.map ((c.toB.map.naturality φ).hom.toNatTrans.app x) ≫
        (S1864SiteComparisonRight g φ).inv.app ((c.toB.map.app U).toFunctor.obj x) := by
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

noncomputable def liftNatConeA {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    (((W.source.fiber.map φ).toFunctor ⋙ liftApp (f := f) (g := g) c V) ⋙
        S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor) ⟶
      ((liftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor) ⋙
        S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor) :=
  (c.toA.map.naturality φ).hom.toNatTrans

noncomputable def liftNatConeB {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    (((W.source.fiber.map φ).toFunctor ⋙ liftApp (f := f) (g := g) c V) ⋙
        S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor) ⟶
      ((liftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor) ⋙
        S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor) :=
  (c.toB.map.naturality φ).hom.toNatTrans

theorem cone1_commutes_app {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(W.source.fiber.obj U)) :
    ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)).obj
          ((W.source.fiber.map φ).toFunctor ⋙ liftApp (f := f) (g := g) c V)).commutes.hom.app x =
      (c.commutes.hom.as.app V).toNatTrans.app ((W.source.fiber.map φ).toFunctor.obj x) := by
  rw [S1893ComparisonFunctor_obj_commutes_hom_app, S1836IsoCommaNatIso_hom_app]
  change ((liftApp (f := f) (g := g) c V).obj
    ((W.source.fiber.map φ).toFunctor.obj x)).obj.hom = _
  simp only [liftApp]
  rw [S1893Lift_structure]
  rfl

theorem cone2_commutes_app {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(W.source.fiber.obj U)) :
    ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)).obj
          (liftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor)).commutes.hom.app x =
      (S1864SiteComparisonLeft f φ).hom.app ((c.toA.map.app U).toFunctor.obj x) ≫
        (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x) ≫
          (S1864SiteComparisonRight g φ).hom.app ((c.toB.map.app U).toFunctor.obj x) := by
  rw [S1893ComparisonFunctor_obj_commutes_hom_app, S1836IsoCommaNatIso_hom_app]
  change ((S1864IsoCommaRestrict (A.source.fiber.map φ).toFunctor
      (B.source.fiber.map φ).toFunctor (C.source.fiber.map φ).toFunctor
      (S1864SiteComparisonLeft f φ) (S1864SiteComparisonRight g φ)).obj
        ((S1893Lift (f.map.app U).toFunctor (g.map.app U).toFunctor
          (coneAt (f := f) (g := g) c U)).obj x)).obj.hom = _
  rw [S1864IsoCommaRestrict_obj_hom]
  rw [S1893Lift_structure]
  rfl

theorem liftCone_compat {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(W.source.fiber.obj U)) :
    (f.map.app V).toFunctor.map ((c.toA.map.naturality φ).hom.toNatTrans.app x) ≫
        ((S1864SiteComparisonLeft f φ).hom.app ((c.toA.map.app U).toFunctor.obj x) ≫
          (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x) ≫
            (S1864SiteComparisonRight g φ).hom.app ((c.toB.map.app U).toFunctor.obj x)) =
      (c.commutes.hom.as.app V).toNatTrans.app ((W.source.fiber.map φ).toFunctor.obj x) ≫
        (g.map.app V).toFunctor.map ((c.toB.map.naturality φ).hom.toNatTrans.app x) := by
  have h := congrArg (fun m => m.toNatTrans.app x) (c.commutes.hom.as.naturality φ)
  simp only [Functor.whiskerRight_app, NatTrans.toCatHom₂_toNatTrans,
      Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at h
  rw [vcomp_toA_naturality_apply (f := f) (g := g) c φ x,
      vcomp_toB_naturality_apply (f := f) (g := g) c φ x] at h
  calc
    (f.map.app V).toFunctor.map ((c.toA.map.naturality φ).hom.toNatTrans.app x) ≫
        ((S1864SiteComparisonLeft f φ).hom.app ((c.toA.map.app U).toFunctor.obj x) ≫
          (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x) ≫
            (S1864SiteComparisonRight g φ).hom.app ((c.toB.map.app U).toFunctor.obj x))
        = ((((f.map.app V).toFunctor.map ((c.toA.map.naturality φ).hom.toNatTrans.app x) ≫
            (S1864SiteComparisonLeft f φ).hom.app ((c.toA.map.app U).toFunctor.obj x)) ≫
              (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x)) ≫
                (S1864SiteComparisonRight g φ).hom.app ((c.toB.map.app U).toFunctor.obj x)) := by
          simp only [Category.assoc]
    _ = ((c.commutes.hom.as.app V).toNatTrans.app ((W.source.fiber.map φ).toFunctor.obj x) ≫
            ((g.map.app V).toFunctor.map ((c.toB.map.naturality φ).hom.toNatTrans.app x) ≫
              (S1864SiteComparisonRight g φ).inv.app ((c.toB.map.app U).toFunctor.obj x))) ≫
                  (S1864SiteComparisonRight g φ).hom.app ((c.toB.map.app U).toFunctor.obj x) := by
          rw [← h]
    _ = (c.commutes.hom.as.app V).toNatTrans.app ((W.source.fiber.map φ).toFunctor.obj x) ≫
          (g.map.app V).toFunctor.map ((c.toB.map.naturality φ).hom.toNatTrans.app x) := by
          simp only [Category.assoc, Iso.inv_hom_id_app]
          erw [Category.comp_id]


/-! ## Cone hom and comparison -/

noncomputable def liftConeHomForward {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    S1893Cone.Hom
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)).obj
          ((W.source.fiber.map φ).toFunctor ⋙ liftApp (f := f) (g := g) c V))
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)).obj
          (liftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor)) :=
  ⟨(liftNatConeA (f := f) (g := g) c φ, liftNatConeB (f := f) (g := g) c φ), by
    apply NatTrans.ext
    funext x
    dsimp only
    simp only [NatTrans.comp_app, Functor.whiskerRight_app]
    rw [cone1_commutes_app, cone2_commutes_app]
    dsimp only [liftNatConeA, liftNatConeB]
    exact liftCone_compat f g c φ x⟩

end LeanFormal.IUT.XiFPaper.S1985Probe