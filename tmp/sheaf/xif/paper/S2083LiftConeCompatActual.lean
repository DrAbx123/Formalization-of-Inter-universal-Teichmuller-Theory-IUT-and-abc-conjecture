import tmp.sheaf.xif.paper.S2082Cone2Actual

/-! # S2083: liftCone_compat for a general cone

Mirrors S1985 `liftCone_compat` with `S2078ConeAt/LiftApp` and the site
comparison formulas.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2083LiftConeCompatActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2079GeneralLiftNatActual

universe u
variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)

theorem S2083vcomp_toA_naturality_apply (c : S2074GeneralCone f g)
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

theorem S2083vcomp_toB_naturality_apply (c : S2074GeneralCone f g)
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

theorem S2083liftCone_compat (c : S2074GeneralCone f g)
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
  rw [S2083vcomp_toA_naturality_apply (f := f) (g := g) c φ x,
      S2083vcomp_toB_naturality_apply (f := f) (g := g) c φ x] at h
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

end LeanFormal.IUT.XiFPaper.S2083LiftConeCompatActual

end
