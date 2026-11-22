import tmp.sheaf.xif.paper.S1802BicategoricalYonedaActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual

universe u

variable {F : Type u} [Field F]
variable {S : Iut.SchemeOverField F}
variable (G : Iut.EtaleStackPseudofunctor F)


lemma ofApp_map (x : G.obj (site S)) (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    {P Q : Discrete (Opposite.unop a.as ⟶ S)} (f : P ⟶ Q) :
    (ofApp G x a).toFunctor.map f =
      eqToHom (congrArg (fun R : Opposite.unop a.as ⟶ S =>
        (G.map (Quiver.Hom.toLoc R.op)).toFunctor.obj x) (Discrete.eq_of_hom f)) := by
  obtain ⟨⟨h⟩⟩ := f
  rfl

lemma map₂_eqToHom {B : Type*} [Bicategory B] [Bicategory.IsLocallyDiscrete B]
    (H : B ⥤ᵖ Cat.{u, u}) {a b : B} {f g : a ⟶ b} (h : f = g) :
    H.map₂ (eqToHom h) = eqToHom (congrArg H.map h) := by
  cases h
  simp

theorem compCoherence (x : G.obj (site S)) : CompCoherence G x := by
  intro a b c f g
  let a' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop a.as))
  let b' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop b.as))
  let c' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop c.as))
  let f' : a' ⟶ b' := f
  let g' : b' ⟶ c' := g
  change (ofNat G x (f' ≫ g')).hom ≫ ofApp G x a' ◁ (G.mapComp f' g').hom =
    ((Y S).mapComp f' g').hom ▷ ofApp G x c' ≫
      (α_ ((Y S).map f') ((Y S).map g') (ofApp G x c')).hom ≫
        (Y S).map f' ◁ (ofNat G x g').hom ≫
          (α_ ((Y S).map f') (ofApp G x b') (G.map g')).inv ≫
            (ofNat G x f').hom ▷ G.map g' ≫
              (α_ (ofApp G x a') (G.map f') (G.map g')).hom
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext P
  obtain ⟨P⟩ := P
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, CategoryTheory.Cat.leftUnitor_hom_app,
    CategoryTheory.Cat.rightUnitor_inv_app, CategoryTheory.Cat.rightUnitor_hom_app,
    CategoryTheory.Cat.leftUnitor_inv_app, CategoryTheory.Cat.eqToHom_app,
    CategoryTheory.Cat.Hom₂.eqToHom_toNatTrans,
    CategoryTheory.Cat.Hom.toNatIso_hom, ofNat_hom_app,
    CategoryTheory.Cat.associator_hom_app, CategoryTheory.Cat.associator_inv_app]
  simp only [ofApp_obj]
  have hassoc : (G.mapComp (Quiver.Hom.toLoc P.op) (f' ≫ g')).hom ≫
      G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapComp f' g').hom =
      G.map₂ (α_ (Quiver.Hom.toLoc P.op) f' g').inv ≫
        (G.mapComp (Quiver.Hom.toLoc P.op ≫ f') g').hom ≫
          (G.mapComp (Quiver.Hom.toLoc P.op) f').hom ▷ G.map g' ≫
            (α_ (G.map (Quiver.Hom.toLoc P.op)) (G.map f') (G.map g')).hom := by
    rw [Pseudofunctor.mapComp_assoc_right_hom]
  rw [← CategoryTheory.Cat.whiskerLeft_app]
  rw [← CategoryTheory.Cat.Hom₂.comp_app]
  rw [hassoc]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app]
  have hα : (α_ (Quiver.Hom.toLoc P.op) f' g').inv =
      eqToHom (LocallyDiscrete.eq_of_hom (α_ (Quiver.Hom.toLoc P.op) f' g').inv) := Subsingleton.elim _ _
  rw [hα]
  rw [map₂_eqToHom]
  simp only [CategoryTheory.Cat.eqToHom_app, CategoryTheory.Cat.associator_hom_app]
  rw [ofApp_map]
  have hX : (G.mapComp (Quiver.Hom.toLoc P.op ≫ f') g').hom.toNatTrans.app x =
      (G.mapComp (Quiver.Hom.toLoc ((((Y S).map f').toFunctor.obj { as := P }).as.op)) g').hom.toNatTrans.app x := rfl
  rw [hX]
  simp
  exact (Category.id_comp _).symm

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual