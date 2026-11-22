import tmp.sheaf.xif.paper.S1824YonedaCoherenceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true

namespace LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual

universe u

variable {F : Type u} [Field F]
variable {S : Iut.SchemeOverField F}
variable (G : Iut.EtaleStackPseudofunctor F)

example (eta : Pseudofunctor.StrongTrans (Y S) G)
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b) :
    (Y S).map f ◁ (unitNat G eta b).hom ≫ ((ofObjFull G (toObj G eta)).naturality f).hom =
      (eta.naturality f).hom ≫ (unitNat G eta a).hom ▷ G.map f := by
  let a' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop a.as))
  let b' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop b.as))
  let f' : a' ⟶ b' := f
  change (Y S).map f' ◁ (unitNat G eta b').hom ≫ ((ofObjFull G (toObj G eta)).naturality f').hom =
      (eta.naturality f').hom ≫ (unitNat G eta a').hom ▷ G.map f'
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext P
  obtain ⟨P⟩ := P
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, ofNat_hom_app, ofObjFull_naturality,
    CategoryTheory.Cat.Hom.toNatIso_hom]
  rw [unitNat_hom_app]
  rw [unitNat_hom_app]
  simp only [toObj_def]
  simp
  change (eta.naturality (Quiver.Hom.toLoc P.op ≫ f')).hom.toNatTrans.app (Discrete.mk (𝟙 S)) ≫
      (G.mapComp (Quiver.Hom.toLoc P.op) f').hom.toNatTrans.app ((eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S))) =
    (eta.naturality f').hom.toNatTrans.app (Discrete.mk P) ≫
      (G.map f').toFunctor.map ((eta.naturality (Quiver.Hom.toLoc P.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S)))
  have h := congrArg (fun α => α.toNatTrans.app (Discrete.mk (𝟙 S))) (eta.naturality_comp (Quiver.Hom.toLoc P.op) f')
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Functor.map_comp, CategoryTheory.eqToHom_map,
    CategoryTheory.eqToHom_trans] at h
  have hYmap : (eta.app b').toFunctor.map (((Y S).mapComp (Quiver.Hom.toLoc P.op) f').hom.toNatTrans.app (Discrete.mk (𝟙 S))) =
      𝟙 ((((Y S).map f' ≫ eta.app b')).toFunctor.obj ((((Y S).map (Quiver.Hom.toLoc P.op)).toFunctor.obj (Discrete.mk (𝟙 S))))) := by
    rw [show ((Y S).mapComp (Quiver.Hom.toLoc P.op) f').hom.toNatTrans.app (Discrete.mk (𝟙 S)) =
      eqToHom (show ((Y S).map (Quiver.Hom.toLoc P.op ≫ f')).toFunctor.obj (Discrete.mk (𝟙 S)) =
        ((Y S).map (Quiver.Hom.toLoc P.op) ≫ (Y S).map f').toFunctor.obj (Discrete.mk (𝟙 S)) from rfl) from rfl]
    simp only [CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_refl, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.comp_obj]
    rfl
  have hA1 : (α_ ((Y S).map (Quiver.Hom.toLoc P.op)) ((Y S).map f') (eta.app b')).hom.toNatTrans.app (Discrete.mk (𝟙 S)) =
      𝟙 ((((Y S).map f' ≫ eta.app b')).toFunctor.obj ((((Y S).map (Quiver.Hom.toLoc P.op)).toFunctor.obj (Discrete.mk (𝟙 S))))) := by
    rw [CategoryTheory.Cat.associator_hom_app]
    rfl
  have hA2 : (α_ ((Y S).map (Quiver.Hom.toLoc P.op)) (eta.app a') (G.map f')).inv.toNatTrans.app (Discrete.mk (𝟙 S)) =
      𝟙 ((eta.app a' ≫ G.map f').toFunctor.obj ((((Y S).map (Quiver.Hom.toLoc P.op)).toFunctor.obj (Discrete.mk (𝟙 S))))) := by
    rw [CategoryTheory.Cat.associator_inv_app]
    rfl
  have hA3 : (α_ (eta.app (site S)) (G.map (Quiver.Hom.toLoc P.op)) (G.map f')).hom.toNatTrans.app (Discrete.mk (𝟙 S)) =
      𝟙 (((G.map (Quiver.Hom.toLoc P.op) ≫ G.map f')).toFunctor.obj ((eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S)))) := by
    rw [CategoryTheory.Cat.associator_hom_app]
    rfl
  rw [hYmap, hA1, hA2, hA3] at h
  rw [h]
  simp only [Category.id_comp, Category.comp_id]
  rfl