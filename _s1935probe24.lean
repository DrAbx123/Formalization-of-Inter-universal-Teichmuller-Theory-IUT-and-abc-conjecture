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

theorem cat_associator_hom_app' {B C D E : Cat.{v, v}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E)
    (X : ↑B) : (α_ F G H).hom.toNatTrans.app X = 𝟙 _ := by simp

theorem cat_associator_inv_app' {B C D E : Cat.{v, v}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E)
    (X : ↑B) : (α_ F G H).inv.toNatTrans.app X = 𝟙 _ := by simp

/-- Componentwise form of naturality_comp_hom with the trailing inverse comparison
cancelled against the comparison itself. -/
theorem natCompHomApp_comp {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{v, v}}
    (α : Pseudofunctor.StrongTrans F G)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (x : ↑(F.obj a)) :
    (α.naturality (f ≫ g)).hom.toNatTrans.app x ≫
        (G.mapComp f g).hom.toNatTrans.app ((α.app a).toFunctor.obj x) =
      (α.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app x) ≫
        (α.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj x) ≫
          (G.map g).toFunctor.map ((α.naturality f).hom.toNatTrans.app x) := by
  rw [← CategoryTheory.Cat.whiskerLeft_app]
  rw [← CategoryTheory.Cat.Hom₂.comp_app]
  rw [Pseudofunctor.StrongTrans.naturality_comp_hom]
  simp only [Category.assoc]
  rw [← CategoryTheory.Bicategory.whiskerLeft_comp]
  rw [Iso.inv_hom_id]
  rw [CategoryTheory.Bicategory.whiskerLeft_id]
  rw [Category.comp_id]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, cat_associator_hom_app', cat_associator_inv_app',
    Category.id_comp, Category.comp_id]

/-- Componentwise form of naturality_comp_inv with the trailing inverse comparison
cancelled against the comparison itself (beta direction). -/
theorem natCompInvApp_comp {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{v, v}}
    (α : Pseudofunctor.StrongTrans F G)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (x : ↑(F.obj a)) :
    (G.mapComp f g).hom.toNatTrans.app ((α.app a).toFunctor.obj x) ≫
        (G.map g).toFunctor.map ((α.naturality f).inv.toNatTrans.app x) ≫
          (α.naturality g).inv.toNatTrans.app ((F.map f).toFunctor.obj x) =
      (α.naturality (f ≫ g)).inv.toNatTrans.app x ≫
        (α.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app x) := by
  rw [← CategoryTheory.Cat.whiskerRight_app]
  rw [← CategoryTheory.Cat.Hom₂.comp_app]
  rw [Pseudofunctor.StrongTrans.naturality_comp_inv]
  simp only [Category.assoc]
  rw [← CategoryTheory.Bicategory.comp_whiskerRight]
  rw [Iso.inv_hom_id]
  rw [CategoryTheory.Bicategory.id_whiskerRight]
  rw [Category.comp_id]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, cat_associator_hom_app', cat_associator_inv_app',
    Category.id_comp, Category.comp_id]

/-- Componentwise form of naturality_id_inv with the mapId inverse comparison
cancelled against the mapId comparison itself. -/
theorem natCompIdApp_comp {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{v, v}}
    (α : Pseudofunctor.StrongTrans F G)
    {a : B} (x : ↑(F.obj a)) :
    (α.naturality (𝟙 a)).inv.toNatTrans.app x ≫
        (α.app a).toFunctor.map ((F.mapId a).hom.toNatTrans.app x) =
      (G.mapId a).hom.toNatTrans.app ((α.app a).toFunctor.obj x) := by
  rw [← CategoryTheory.Cat.whiskerLeft_app]
  rw [← CategoryTheory.Cat.whiskerRight_app]
  rw [← CategoryTheory.Cat.Hom₂.comp_app]
  rw [Pseudofunctor.StrongTrans.naturality_id_inv]
  simp only [Category.assoc]
  rw [← CategoryTheory.Bicategory.comp_whiskerRight]
  rw [Iso.inv_hom_id]
  rw [CategoryTheory.Bicategory.id_whiskerRight]
  rw [Category.comp_id]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, cat_leftUnitor_inv_app', cat_rightUnitor_hom_app',
    Category.id_comp, Category.comp_id]

end
