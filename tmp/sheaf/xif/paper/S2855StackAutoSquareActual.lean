import tmp.sheaf.xif.paper.S2854StackAutoFromSchemeActual
import tmp.sheaf.xif.paper.S1742HomVcompActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2855StackAutoSquareActual

open LeanFormal.IUT.XiFPaper.S2854StackAutoFromSchemeActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S2851A6D6GeometryActual

local instance : Field K := inferInstance
local instance : DecidableEq K := Classical.decEq _

theorem S2855HomOf_vcomp_self
    (α : S2844X ⟶ S2844X) (hα : α ≫ α = 𝟙 S2844X) :
    S1742HomOfStrongTrans (F := K)
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := K) α)
        (S1742StrongTransOfHom (F := K) α)) = 𝟙 S2844X := by
  simpa [S1742HomOfStrongTrans_vcomp,
    S1742HomOfStrongTrans_strongTransOfHom] using hα

noncomputable def S2855StackAuto_square
    (α : S2844X ⟶ S2844X) (hα : α ≫ α = 𝟙 S2844X) :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp (S2854StackAuto α) (S2854StackAuto α))
      (Iut.HyperbolicOrbicurve.Hom.id S2851HyperbolicOrbicurve) := by
  change Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := K) α)
      (S1742StrongTransOfHom (F := K) α) ≅
    Pseudofunctor.StrongTrans.id
      (S1742YS (F := K) S2844X)
  have hcomp := S2855HomOf_vcomp_self α hα
  let A := S1742StrongTransIsoOfHom (F := K)
    (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := K) α)
      (S1742StrongTransOfHom (F := K) α))
  let B := S1742StrongTransIsoOfHom (F := K)
    (Pseudofunctor.StrongTrans.id (S1742YS (F := K) S2844X))
  exact (hcomp ▸ A).symm.trans B

#check S2855StackAuto_square
#print axioms S2855StackAuto_square

end LeanFormal.IUT.XiFPaper.S2855StackAutoSquareActual
end
