import tmp.sheaf.xif.paper.S1742TwoYonedaActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

namespace LeanFormal.IUT.XiFPaper.S1742HomVcompActual

variable {F : Type} [Field F]

theorem S1742HomOfStrongTrans_vcomp
    {X Y Z : Iut.SchemeOverField F}
    (eta : Pseudofunctor.StrongTrans (S1742YS (F := F) X) (S1742YS (F := F) Y))
    (theta : Pseudofunctor.StrongTrans (S1742YS (F := F) Y) (S1742YS (F := F) Z)) :
    S1742HomOfStrongTrans (F := F)
        (Pseudofunctor.StrongTrans.vcomp eta theta) =
      S1742HomOfStrongTrans (F := F) eta ≫
        S1742HomOfStrongTrans (F := F) theta := by
  unfold S1742HomOfStrongTrans
  rw [show (Pseudofunctor.StrongTrans.vcomp eta theta).app (LocallyDiscrete.mk (Opposite.op X)) = eta.app (LocallyDiscrete.mk (Opposite.op X)) ≫ theta.app (LocallyDiscrete.mk (Opposite.op X)) from rfl]
  rw [CategoryTheory.Cat.Hom.comp_obj]
  rw [S1742Key eta (LocallyDiscrete.mk (Opposite.op X)) (𝟙 X)]
  rw [← Discrete.mk_as ((eta.app (LocallyDiscrete.mk (Opposite.op X))).toFunctor.obj
      (Discrete.mk (𝟙 X)))]
  rw [S1742Key theta (LocallyDiscrete.mk (Opposite.op X))
    (((eta.app (LocallyDiscrete.mk (Opposite.op X))).toFunctor.obj
      (Discrete.mk (𝟙 X))).as)]
  rfl

#print axioms S1742HomOfStrongTrans_vcomp

end LeanFormal.IUT.XiFPaper.S1742HomVcompActual
end