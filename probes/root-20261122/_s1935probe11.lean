import tmp.sheaf.xif.paper.S1922IsoCommaCoherenceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open CategoryTheory.Bicategory
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual

universe u v

theorem natCompHomApp' {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{v, v}}
    (α : Pseudofunctor.StrongTrans F G)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (x : ↑(F.obj a)) :
    (α.naturality (f ≫ g)).hom.toNatTrans.app x =
      (α.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app x) ≫
        (α.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj x) ≫
          (G.map g).toFunctor.map ((α.naturality f).hom.toNatTrans.app x) ≫
            (G.mapComp f g).inv.toNatTrans.app ((α.app a).toFunctor.obj x) := by
  rw [Pseudofunctor.StrongTrans.naturality_comp_hom]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, CategoryTheory.Cat.associator_hom_app,
    CategoryTheory.Cat.associator_inv_app]
  simp

theorem natCompInvApp' {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{v, v}}
    (α : Pseudofunctor.StrongTrans F G)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (x : ↑(F.obj a)) :
    (α.naturality (f ≫ g)).inv.toNatTrans.app x =
      (G.mapComp f g).hom.toNatTrans.app ((α.app a).toFunctor.obj x) ≫
        (G.map g).toFunctor.map ((α.naturality f).inv.toNatTrans.app x) ≫
          (α.naturality g).inv.toNatTrans.app ((F.map f).toFunctor.obj x) ≫
            (α.app c).toFunctor.map ((F.mapComp f g).inv.toNatTrans.app x) := by
  rw [Pseudofunctor.StrongTrans.naturality_comp_inv]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, CategoryTheory.Cat.associator_hom_app,
    CategoryTheory.Cat.associator_inv_app]
  simp

section SiteCompF

variable {A C : S1728Cover} (f : S1728CoverMap A C)
  {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)

theorem siteCompF_probe (x : ↥(A.source.fiber.obj U)) : S1890SiteCompF f φ ψ x := by
  unfold S1890SiteCompF
  rw [natCompHomApp']
  simp only [Category.assoc]
  rw [CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app]
  rw [CategoryTheory.Cat.Hom.comp_obj, Category.comp_id]

end SiteCompF

section SiteCompG

variable {B C : S1728Cover} (g : S1728CoverMap B C)
  {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)

theorem siteCompG_probe (y : ↥(B.source.fiber.obj U)) : S1890SiteCompG g φ ψ y := by
  unfold S1890SiteCompG
  rw [natCompInvApp']
  simp only [Category.assoc]
  rw [← Functor.map_comp]
  rw [CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app, Functor.map_id]
  rw [CategoryTheory.Cat.Hom.comp_obj, Category.comp_id]

end SiteCompG

section SiteIdG

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

theorem siteIdG_probe (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) : S1890SiteIdG f g U := by
  intro x y h
  rw [Pseudofunctor.StrongTrans.naturality_id_inv]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, cat_leftUnitor_inv_app, cat_rightUnitor_hom_app]
  simp only [Category.assoc]
  rw [← Functor.map_comp, CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app, Functor.map_id]
  rw [CategoryTheory.Cat.Hom.id_obj, Category.comp_id]

end SiteIdG

end
