import tmp.sheaf.xif.paper.S1824YonedaCoherenceActual

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

example (eta : Pseudofunctor.StrongTrans (Y S) G)
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b) :
    (Y S).map f ◁ (unitNat G eta b).hom ≫ ((ofObjFull G (toObj G eta)).naturality f).hom =
      (eta.naturality f).hom ≫ (unitNat G eta a).hom ▷ G.map f := by
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext P
  obtain ⟨P⟩ := P
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, ofNat_hom_app, ofObjFull_naturality,
    CategoryTheory.Cat.Hom.toNatIso_hom]
  rw [unitNat_hom_app]
  rw [unitNat_hom_app]
  simp
  simpa only [CategoryTheory.Cat.Hom.toNatIso_hom, CategoryTheory.Cat.Hom₂.comp_app,
    CategoryTheory.Cat.whiskerLeft_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.associator_hom_app, CategoryTheory.Cat.associator_inv_app,
    ofApp_obj, ofObjFull_app, CategoryTheory.Functor.map_comp, CategoryTheory.eqToHom_map,
    CategoryTheory.eqToHom_trans] using congrArg (fun α => α.toNatTrans.app (Discrete.mk (𝟙 S)))
    (eta.naturality_comp (Quiver.Hom.toLoc P.op) f)

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual