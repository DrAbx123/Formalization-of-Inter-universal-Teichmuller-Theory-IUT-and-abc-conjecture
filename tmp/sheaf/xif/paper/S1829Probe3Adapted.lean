import tmp.sheaf.xif.paper.S1802BicategoricalYonedaActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option pp.proofs false
set_option pp.universes false

namespace LeanFormal.IUT.XiFPaper.S1829Probe3Adapted

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual

universe u

variable {F : Type u} [Field F]
variable {S : Iut.SchemeOverField F}
variable (G : Iut.EtaleStackPseudofunctor F)

lemma map₂_eqToHom {B : Type*} [Bicategory B] [Bicategory.IsLocallyDiscrete B]
    (H : B ⥤ᵖ Cat.{u, u}) {a b : B} {f g : a ⟶ b} (h : f = g) :
    H.map₂ (eqToHom h) = eqToHom (congrArg H.map h) := by
  cases h
  simp

lemma ofApp_map (x : G.obj (site S)) (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    {P Q : Discrete (Opposite.unop a.as ⟶ S)} (f : P ⟶ Q) :
    (ofApp G x a).toFunctor.map f =
      eqToHom (congrArg (fun R : Opposite.unop a.as ⟶ S =>
        (G.map (Quiver.Hom.toLoc R.op)).toFunctor.obj x) (Discrete.eq_of_hom f)) := by
  obtain ⟨⟨h⟩⟩ := f
  rfl

lemma rightUnitor_inv_app_eq_id {C D : Cat.{u, u}} (F : C ⟶ D) (X : C) :
    (ρ_ F).inv.toNatTrans.app X = 𝟙 _ := by
  rw [CategoryTheory.Cat.rightUnitor_inv_app]
  exact eqToHom_refl _ _

lemma leftUnitor_hom_app_eq_id {C D : Cat.{u, u}} (F : C ⟶ D) (X : C) :
    (λ_ F).hom.toNatTrans.app X = 𝟙 _ := by
  rw [CategoryTheory.Cat.leftUnitor_hom_app]
  exact eqToHom_refl _ _

theorem idCoherence_probe (x : G.obj (site S)) : IdCoherence G x := by
  intro a
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext P
  obtain ⟨P⟩ := P
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, CategoryTheory.Cat.leftUnitor_hom_app,
    CategoryTheory.Cat.rightUnitor_inv_app, CategoryTheory.Cat.rightUnitor_hom_app,
    CategoryTheory.Cat.leftUnitor_inv_app, CategoryTheory.Cat.eqToHom_app,
    CategoryTheory.Cat.Hom₂.eqToHom_toNatTrans, ofNat_hom_app]
  dsimp only [CategoryTheory.Cat.Hom.toNatIso]
  rw [G.mapComp_id_right_hom]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app]
  have hρ : (ρ_ (Quiver.Hom.toLoc P.op)).hom =
      eqToHom (LocallyDiscrete.eq_of_hom (ρ_ (Quiver.Hom.toLoc P.op)).hom) :=
    Subsingleton.elim _ _
  rw [hρ, map₂_eqToHom]
  simp only [CategoryTheory.Cat.eqToHom_app]
  rw [rightUnitor_inv_app_eq_id]
  rw [ofApp_map]
  have hmapid : G.mapId { as := Opposite.op (Opposite.unop a.as) } = G.mapId a := rfl
  rw [hmapid]
  rw [Category.assoc, Category.assoc, Category.id_comp]
  have hobj : (ofApp G x a).toFunctor.obj (Discrete.mk P) =
      (G.map (Quiver.Hom.toLoc P.op)).toFunctor.obj x := rfl
  rw [hobj]
  rw [CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app]
  trace_state
  simp only [Category.id_comp, Category.comp_id]
  trace_state
  sorry

end LeanFormal.IUT.XiFPaper.S1829Probe3Adapted