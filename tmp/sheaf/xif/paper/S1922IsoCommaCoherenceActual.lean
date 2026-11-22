import tmp.sheaf.xif.paper.S1890IsoCommaPseudofunctorActual

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

universe u

theorem cat_leftUnitor_hom_app {B C : Cat.{u, u}} (F : B ⟶ C) (X : ↑B) :
    (λ_ F).hom.toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by simp

theorem cat_leftUnitor_inv_app {B C : Cat.{u, u}} (F : B ⟶ C) (X : ↑B) :
    (λ_ F).inv.toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by simp

theorem cat_rightUnitor_hom_app {B C : Cat.{u, u}} (F : B ⟶ C) (X : ↑B) :
    (ρ_ F).hom.toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by simp

theorem cat_rightUnitor_inv_app {B C : Cat.{u, u}} (F : B ⟶ C) (X : ↑B) :
    (ρ_ F).inv.toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by simp

theorem cat_associator_hom_app {B C D E : Cat.{u, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E)
    (X : ↑B) : (α_ F G H).hom.toNatTrans.app X = 𝟙 _ := by simp

theorem cat_associator_inv_app {B C D E : Cat.{u, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E)
    (X : ↑B) : (α_ F G H).inv.toNatTrans.app X = 𝟙 _ := by simp

theorem natCompHomApp {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{u, u}}
    (α : Pseudofunctor.StrongTrans F G)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (x : ↑(F.obj a)) :
    (α.naturality (f ≫ g)).hom.toNatTrans.app x =
      (α.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app x) ≫
        (α.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj x) ≫
          (G.map g).toFunctor.map ((α.naturality f).hom.toNatTrans.app x) ≫
            (G.mapComp f g).inv.toNatTrans.app ((α.app a).toFunctor.obj x) := by
  rw [Pseudofunctor.StrongTrans.naturality_comp_hom]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, cat_associator_hom_app, cat_associator_inv_app]
  simp

theorem natCompInvApp {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{u, u}}
    (α : Pseudofunctor.StrongTrans F G)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (x : ↑(F.obj a)) :
    (α.naturality (f ≫ g)).inv.toNatTrans.app x =
      (G.mapComp f g).hom.toNatTrans.app ((α.app a).toFunctor.obj x) ≫
        (G.map g).toFunctor.map ((α.naturality f).inv.toNatTrans.app x) ≫
          (α.naturality g).inv.toNatTrans.app ((F.map f).toFunctor.obj x) ≫
            (α.app c).toFunctor.map ((F.mapComp f g).inv.toNatTrans.app x) := by
  rw [Pseudofunctor.StrongTrans.naturality_comp_inv]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, cat_associator_hom_app, cat_associator_inv_app]
  simp

theorem siteIdF {A C : S1728Cover} (f : S1728CoverMap A C)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↥(A.source.fiber.obj U)) :
    S1890SiteIdF f U x := by
  unfold S1890SiteIdF
  rw [Pseudofunctor.StrongTrans.naturality_id_hom]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, CategoryTheory.Cat.leftUnitor_hom_app,
    CategoryTheory.Cat.rightUnitor_inv_app, CategoryTheory.eqToHom_refl,
    CategoryTheory.Cat.Hom.id_obj, CategoryTheory.Cat.Hom.comp_obj, Functor.comp_obj,
    Functor.id_obj, CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app, Category.comp_id,
    Category.id_comp, Category.assoc]
  exact (Category.comp_id (f := (f.map.app U).toFunctor.map
    ((A.source.fiber.mapId U).hom.toNatTrans.app x))).symm

/-- **The exact first missing, after the reductions proved in this file.**

* (m0a) `S1890SiteCompF`: after `natCompHomApp` the two sides differ exactly by the
  trailing factor `(C.source.fiber.mapComp φ ψ).inv ≫ (C.source.fiber.mapComp φ ψ).hom`,
  whose cancellation needs the `Cat`-object identification
  `(C.map φ ≫ C.map ψ).toFunctor.obj X = (C.map ψ).toFunctor.obj ((C.map φ).toFunctor.obj X)`
  (`CategoryTheory.Cat.Hom.comp_obj`, which is proved by `simp`, hence *not* definitional).
* (m0b) `S1890SiteCompG`: same, in the inverse direction.
* (m1) `S1890SiteIdG`: after `naturality_id_inv` the two sides differ exactly by
  `(g.map.app U).toFunctor.map 𝟙 = 𝟙` together with the `Cat.Hom.id_obj` identification
  `(𝟙 X).toFunctor.obj Y = Y`; this is the mirror image of `siteIdF`, proved above,
  and again fails only because `Cat.Hom.id_obj` is not definitional.
* (m2) the three coherence equations `S1890PseudofunctorCoherence`, which are
  `LocallyDiscrete.mkPseudofunctor`'s last three arguments.

The single Lean-level obstruction for (m0a), (m0b), (m1) is that
`CategoryTheory.Cat` is `def Cat := Bundled Category` and the functor-object
identifications `Cat.Hom.comp_obj`, `Cat.Hom.id_obj` are propositional, so the
motive of `Category.comp_id` / `Category.id_comp` does not typecheck when the
identity 2-cell is presented in the folded `(F ≫ G).toFunctor.obj` form. -/
def S1922FirstMissing (f : S1728CoverMap A C) (g : S1728CoverMap B C) : Prop :=
  (∀ {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)
      (x : ↥(A.source.fiber.obj U)), S1890SiteCompF f φ ψ x) ∧
    (∀ {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)
      (y : ↥(B.source.fiber.obj U)), S1890SiteCompG g φ ψ y) ∧
      (∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ), S1890SiteIdG f g U)

#check cat_leftUnitor_hom_app
#check natCompHomApp
#check natCompInvApp
#check siteIdF
#check S1922FirstMissing

#print axioms cat_associator_hom_app
#print axioms natCompHomApp
#print axioms natCompInvApp
#print axioms siteIdF

end
