import tmp.sheaf.xif.paper.S1763HomVcompActual
import tmp.sheaf.xif.paper.S1762OverModelHomActual

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

namespace LeanFormal.IUT.XiFPaper.S1764QuotToOverProbeAdapted

variable {A B : S1728Cover}

noncomputable def S1764OverBaseOfCoverMap (f : S1728CoverMap A B) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K)
          (S1755ModelHomOfCoverMap A B f))
        (S1755BaseChange B).projectionMap.transformation)
      (S1755BaseChange A).projectionMap.transformation) := by
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  rw [S1755ModelHomOfCoverMap_def]
  let e : S1742StrongTransOfHom (F := S1726K)
      (S1742HomOfStrongTrans (F := S1726K) (S1755Lift A B f))
      ≅ S1755Lift A B f :=
    S1742StrongTransIsoOfHom (F := S1726K) (S1755Lift A B f)
  exact ⟨Bicategory.whiskerRightIso e
      (S1755BaseChange B).projectionMap.transformation
    ≪≫ S1755Lift_toY A B f⟩

noncomputable def S1764QuotToOver (A B : S1728Cover) :
    S1756CoverMapQuot A B -> S1762ModelHomOver A B :=
  Quot.lift
    (fun f =>
      { hom := S1755ModelHomOfCoverMap A B f
        overBase := S1764OverBaseOfCoverMap f })
    (by
      intro f g hr
      have hhom : S1755ModelHomOfCoverMap A B f =
          S1755ModelHomOfCoverMap A B g := S1761LiftWellDefined A B f g hr
      cases hhom
      rfl)

#print axioms S1764QuotToOver

end LeanFormal.IUT.XiFPaper.S1764QuotToOverProbeAdapted
end
