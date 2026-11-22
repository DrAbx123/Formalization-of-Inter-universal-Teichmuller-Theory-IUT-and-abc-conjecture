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

theorem cat_leftUnitor_hom_app' {B C : Cat.{v, v}} (F : B ⟶ C) (X : ↑B) :
    (λ_ F).hom.toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by simp

theorem cat_leftUnitor_inv_app' {B C : Cat.{v, v}} (F : B ⟶ C) (X : ↑B) :
    (λ_ F).inv.toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by simp

theorem cat_rightUnitor_hom_app' {B C : Cat.{v, v}} (F : B ⟶ C) (X : ↑B) :
    (ρ_ F).hom.toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by simp

theorem cat_rightUnitor_inv_app' {B C : Cat.{v, v}} (F : B ⟶ C) (X : ↑B) :
    (ρ_ F).inv.toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by simp

theorem natCompIdApp_comp {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{v, v}}
    (α : Pseudofunctor.StrongTrans F G)
    {a : B} (x : ↑(F.obj a)) :
    (α.naturality (𝟙 a)).inv.toNatTrans.app x ≫
        (α.app a).toFunctor.map ((F.mapId a).hom.toNatTrans.app x) =
      (G.mapId a).hom.toNatTrans.app ((α.app a).toFunctor.obj x) := by
  have hhom : (G.mapId a).hom.toNatTrans.app ((α.app a).toFunctor.obj x)
      = (α.app a ◁ (G.mapId a).hom).toNatTrans.app x := by
    rw [CategoryTheory.Cat.whiskerLeft_app]
  rw [hhom]
  have hcomp : (α.naturality (𝟙 a)).inv.toNatTrans.app x ≫
        (α.app a).toFunctor.map ((F.mapId a).hom.toNatTrans.app x)
      = ((α.naturality (𝟙 a)).inv ≫ (F.mapId a).hom ▷ α.app a).toNatTrans.app x := by
    rw [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app]
  rw [hcomp]
  rw [Pseudofunctor.StrongTrans.naturality_id_inv]
  simp only [Category.assoc]
  rw [CategoryTheory.Bicategory.inv_hom_whiskerRight]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, cat_leftUnitor_inv_app', cat_rightUnitor_hom_app',
    Category.id_comp, Category.comp_id]

end
