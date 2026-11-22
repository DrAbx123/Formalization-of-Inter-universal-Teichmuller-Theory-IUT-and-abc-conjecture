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
variable {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b)
variable (P : Discrete (Opposite.unop a.as ⟶ S))
variable (eta : Pseudofunctor.StrongTrans (Y S) G)

example :
    (eta.app b).toFunctor.map (((Y S).mapComp (Quiver.Hom.toLoc P.as.op) f).hom.toNatTrans.app (Discrete.mk (𝟙 S))) =
      𝟙 ((((Y S).map f ≫ eta.app b)).toFunctor.obj ((((Y S).map (Quiver.Hom.toLoc P.as.op)).toFunctor.obj (Discrete.mk (𝟙 S))))) := by
  rw [show ((Y S).mapComp (Quiver.Hom.toLoc P.as.op) f).hom.toNatTrans.app (Discrete.mk (𝟙 S)) =
    eqToHom (show ((Y S).map (Quiver.Hom.toLoc P.as.op ≫ f)).toFunctor.obj (Discrete.mk (𝟙 S)) =
      ((Y S).map (Quiver.Hom.toLoc P.as.op) ≫ (Y S).map f).toFunctor.obj (Discrete.mk (𝟙 S)) from rfl) from rfl]
  simp only [CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_refl, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.comp_obj]
  rfl

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual
