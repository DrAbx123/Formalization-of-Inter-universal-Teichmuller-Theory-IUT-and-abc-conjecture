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
variable {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (eta : Pseudofunctor.StrongTrans (Y S) G)
variable (f : a ⟶ b)
variable (P : Discrete (Opposite.unop a.as ⟶ S))

example :
    (G.map f).toFunctor.map ((eta.naturality (Quiver.Hom.toLoc P.as.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S))) ≫
      𝟙 ((G.map f).toFunctor.obj ((G.map (Quiver.Hom.toLoc P.as.op)).toFunctor.obj ((eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S))))) =
    (G.map f).toFunctor.map ((eta.naturality (Quiver.Hom.toLoc P.as.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S))) := by
  have h : (G.map f).toFunctor.map ((eta.naturality (Quiver.Hom.toLoc P.as.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S))) ≫
      𝟙 ((G.map f).toFunctor.obj ((G.map (Quiver.Hom.toLoc P.as.op)).toFunctor.obj ((eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S))))) =
    (G.map f).toFunctor.map ((eta.naturality (Quiver.Hom.toLoc P.as.op)).hom.toNatTrans.app (Discrete.mk (𝟙 S))) := Category.comp_id _
  exact h

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual
