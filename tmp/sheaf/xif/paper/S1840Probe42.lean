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

example : (eta.naturality f).hom.toNatTrans.app P ≫
    𝟙 ((eta.app a ≫ G.map f).toFunctor.obj P) =
    (eta.naturality f).hom.toNatTrans.app P := by
  simp

example : 𝟙 ((Y S).map f ≫ eta.app b).toFunctor.obj P ≫
    (eta.naturality f).hom.toNatTrans.app P =
    (eta.naturality f).hom.toNatTrans.app P := by
  simp

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual
