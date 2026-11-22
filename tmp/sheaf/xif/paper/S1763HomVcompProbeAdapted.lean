import tmp.sheaf.xif.paper.S1742TwoYonedaActual

noncomputable section
open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1763HomVcompProbeAdapted

variable {F : Type} [Field F]
variable {S T U : SchemeOverField F}

theorem S1763HomOfStrongTrans_vcomp
    (L1 : Pseudofunctor.StrongTrans
      (S1742YS (F := F) S) (S1742YS (F := F) T))
    (L2 : Pseudofunctor.StrongTrans
      (S1742YS (F := F) T) (S1742YS (F := F) U)) :
    S1742HomOfStrongTrans (Pseudofunctor.StrongTrans.vcomp L1 L2) =
      S1742HomOfStrongTrans L1 ≫ S1742HomOfStrongTrans L2 := by
  rw [← S1742HomOfStrongTrans_def (Pseudofunctor.StrongTrans.vcomp L1 L2)]
  change ((L2.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
      ((L1.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
        (Discrete.mk (𝟙 S)))).as =
    S1742HomOfStrongTrans L1 ≫ S1742HomOfStrongTrans L2
  erw [S1742Key L1 (LocallyDiscrete.mk (Opposite.op S)) (𝟙 S)]
  erw [S1742Key L2 (LocallyDiscrete.mk (Opposite.op S))
    (𝟙 S ≫ S1742HomOfStrongTrans L1)]
  simp [Category.id_comp, Category.assoc]

#print axioms S1763HomOfStrongTrans_vcomp

end LeanFormal.IUT.XiFPaper.S1763HomVcompProbeAdapted
end
