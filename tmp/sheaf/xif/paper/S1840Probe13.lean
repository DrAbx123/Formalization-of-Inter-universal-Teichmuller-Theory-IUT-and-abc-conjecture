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
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b)
    (P : Discrete (Opposite.unop a.as ⟶ S)) :
    ((Y S).mapComp (Quiver.Hom.toLoc P.as.op) f).hom.toNatTrans.app (Discrete.mk (𝟙 S)) =
      𝟙 (((Y S).map (Quiver.Hom.toLoc P.as.op)).toFunctor.obj (Discrete.mk (𝟙 S)) ⋯) := by
  sorry

example (eta : Pseudofunctor.StrongTrans (Y S) G)
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b)
    (P : Discrete (Opposite.unop a.as ⟶ S)) :
    ((Y S).mapComp (Quiver.Hom.toLoc P.as.op) f).hom.toNatTrans.app (Discrete.mk (𝟙 S)) =
      𝟙 (((Y S).map (Quiver.Hom.toLoc P.as.op)).toFunctor.obj (Discrete.mk (𝟙 S))) := by
  simp

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual
