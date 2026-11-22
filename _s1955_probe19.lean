import tmp.sheaf.xif.paper.S1945SitePseudofunctorDataActual
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
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
    change (A.source.fiber.mapComp f_1 g_1).hom.toNatTrans.app X.obj.left =
      (S1836IsoCommaFst (f.map.app a).toFunctor (g.map.app a).toFunctor).map
        ((siteMapComp f g f_1 g_1).hom.toNatTrans.app X)
    rw [siteMapComp_fst]
end Probe
