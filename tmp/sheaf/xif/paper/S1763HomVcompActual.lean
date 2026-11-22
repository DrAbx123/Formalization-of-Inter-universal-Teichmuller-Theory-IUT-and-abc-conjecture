import tmp.sheaf.xif.paper.S1762OverModelHomActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756QuotientActual
open LeanFormal.IUT.XiFPaper.S1761SubsingletonIsoActual
open LeanFormal.IUT.XiFPaper.S1762OverModelHomActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1763HomVcompActual

theorem S1763HomOfStrongTrans_vcomp
    {F : Type} [Field F]
    {S T U : SchemeOverField F}
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
  let a := LocallyDiscrete.mk (Opposite.op S)
  have h1obj : (L1.app a).toFunctor.obj (Discrete.mk (𝟙 S)) =
      Discrete.mk (S1742HomOfStrongTrans L1) := by
    apply Discrete.ext
    exact S1742Key L1 a (𝟙 S)
  rw [h1obj]
  have h2obj : (L2.app a).toFunctor.obj
      (Discrete.mk (S1742HomOfStrongTrans L1)) =
      Discrete.mk (S1742HomOfStrongTrans L1 ≫ S1742HomOfStrongTrans L2) := by
    apply Discrete.ext
    exact S1742Key L2 a (S1742HomOfStrongTrans L1)
  rw [h2obj]

#print axioms S1763HomOfStrongTrans_vcomp

end LeanFormal.IUT.XiFPaper.S1763HomVcompActual
end
