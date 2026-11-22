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

example (x : G.obj (site S)) :
    toObj G (ofObjFull G x) = (G.map (𝟙 (site S))).toFunctor.obj x := rfl

example : (fun x : G.obj (site S) => toObj G (ofObjFull G x)) = fun x => (G.map (𝟙 (site S))).toFunctor.obj x := rfl

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual
