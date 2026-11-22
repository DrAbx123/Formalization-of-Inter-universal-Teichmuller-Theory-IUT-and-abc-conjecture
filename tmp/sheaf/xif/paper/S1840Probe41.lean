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
variable {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ}

example {X Y : ↑(G.obj b)} (k : X ⟶ Y) : k ≫ 𝟙 Y = k := by simp

example {X Y : ↑(G.obj b)} (k : X ⟶ Y) : 𝟙 X ≫ k = k := by simp

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual
