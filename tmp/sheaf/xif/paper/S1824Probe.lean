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

theorem idCoherence (x : G.obj (site S)) : IdCoherence G x := by
  intro a
  let b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop a.as))
  change (ofNat G x (𝟙 b)).hom ≫ ofApp G x b ◁ (G.mapId b).hom =
    ((Y S).mapId b).hom ▷ ofApp G x b ≫ (λ_ (ofApp G x b)).hom ≫ (ρ_ (ofApp G x b)).inv
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext P
  obtain ⟨P⟩ := P
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, CategoryTheory.Cat.leftUnitor_hom_app,
    CategoryTheory.Cat.rightUnitor_inv_app, CategoryTheory.Cat.rightUnitor_hom_app,
    CategoryTheory.Cat.leftUnitor_inv_app, CategoryTheory.Cat.eqToHom_app,
    CategoryTheory.Cat.Hom₂.eqToHom_toNatTrans,
    CategoryTheory.Cat.Hom.toNatIso_hom, ofNat_hom_app]
  simp only [ofApp_obj]
  have hcomp : (G.mapComp (Quiver.Hom.toLoc P.op) (𝟙 b)).hom =
      G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫ (ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv ≫
        G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).inv := by
    rw [Pseudofunctor.mapComp_id_right_hom]
  have hC : (G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).inv) ≫
      (G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).hom) = 𝟙 _ := by
    rw [← Bicategory.whiskerLeft_comp, Iso.inv_hom_id, Bicategory.whiskerLeft_id]
  have hcoh : (G.mapComp (Quiver.Hom.toLoc P.op) (𝟙 b)).hom ≫
      G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).hom =
      G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫ (ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv := by
    rw [hcomp]
    calc
      (G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫ (ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv ≫
          G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).inv) ≫
          G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).hom
          = G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫
              ((ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv ≫
                ((G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).inv) ≫
                  G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).hom)) := by
            simp only [Category.assoc]
      _ = G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫
              ((ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv ≫ 𝟙 _) := by rw [hC]
      _ = G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫ (ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv := by
            simpa only [Category.assoc] using
              (Category.comp_id (obj := (G.obj (site S) ⟶ G.obj b))
                (f := (G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫ (ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv)))
  rw [← CategoryTheory.Cat.whiskerLeft_app]
  rw [← CategoryTheory.Cat.Hom₂.comp_app]
  rw [hcoh]
  simp only [CategoryTheory.Cat.Hom₂.comp_app]
  have hρ : (ρ_ (Quiver.Hom.toLoc P.op)).hom = eqToHom (LocallyDiscrete.eq_of_hom (ρ_ (Quiver.Hom.toLoc P.op)).hom) :=
    Subsingleton.elim _ _
  rw [hρ]
  rw [map₂_eqToHom]
  simp only [CategoryTheory.Cat.eqToHom_app, CategoryTheory.Cat.rightUnitor_inv_app]
  rw [ofApp_map]
  simp only [CategoryTheory.eqToHom_trans]


theorem compCoherence (x : G.obj (site S)) : CompCoherence G x := by
  intro a b c f g
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
  have hassoc : (G.mapComp (Quiver.Hom.toLoc P.op) (f ≫ g)).hom ≫
      G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapComp f g).hom =
      G.map₂ (α_ (Quiver.Hom.toLoc P.op) f g).inv ≫
        (G.mapComp (Quiver.Hom.toLoc P.op ≫ f) g).hom ≫
          (G.mapComp (Quiver.Hom.toLoc P.op) f).hom ▷ G.map g ≫
            (α_ (G.map (Quiver.Hom.toLoc P.op)) (G.map f) (G.map g)).hom := by
    rw [Pseudofunctor.mapComp_assoc_right_hom]
  rw [← CategoryTheory.Cat.whiskerLeft_app]
  rw [← CategoryTheory.Cat.Hom₂.comp_app]
  rw [hassoc]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app]
  have hα : (α_ (Quiver.Hom.toLoc P.op) f g).inv =
      eqToHom (LocallyDiscrete.eq_of_hom (α_ (Quiver.Hom.toLoc P.op) f g).inv) := Subsingleton.elim _ _
  rw [hα]
  rw [map₂_eqToHom]
  simp only [CategoryTheory.Cat.eqToHom_app, CategoryTheory.Cat.associator_hom_app]
  rw [ofApp_map]
  have hX : (G.mapComp (Quiver.Hom.toLoc P.op ≫ f) g).hom.toNatTrans.app x =
      (G.mapComp (Quiver.Hom.toLoc ((((Y S).map f).toFunctor.obj { as := P }).as.op)) g).hom.toNatTrans.app x := rfl
  rw [hX]
  simp only [CategoryTheory.eqToHom_trans]
  trace_state
  sorry

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual