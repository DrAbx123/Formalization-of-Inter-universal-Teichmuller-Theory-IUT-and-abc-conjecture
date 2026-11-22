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

namespace LeanFormal.IUT.XiFPaper.S1765QuotToOverProbeAdapted

@[ext] theorem S1762ModelHomOver.ext {A B : S1728Cover}
    {x y : S1762ModelHomOver A B} (h : x.hom = y.hom) : x = y := by
  cases x with
  | mk hx ox =>
    cases y with
    | mk hy oy =>
      simp only at h
      subst h
      congr

variable {A B : S1728Cover}

noncomputable def S1765OverBaseOfCoverMap (f : S1728CoverMap A B) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K)
          (S1755ModelHomOfCoverMap A B f))
        (S1755BaseChange B).projectionMap.transformation)
      (S1755BaseChange A).projectionMap.transformation) := by
  rw [S1755ModelHomOfCoverMap_def]
  let e : S1742StrongTransOfHom (F := S1726K)
      (S1742HomOfStrongTrans (F := S1726K) (S1755Lift A B f))
      ≅ S1755Lift A B f :=
    S1742StrongTransIsoOfHom (F := S1726K) (S1755Lift A B f)
  change Nonempty (Iso
    (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1726K)
        (S1742HomOfStrongTrans (F := S1726K) (S1755Lift A B f)))
      (S1755BaseChange B).projectionMap.transformation)
    (S1755BaseChange A).projectionMap.transformation)
  exact ⟨(Bicategory.whiskerRightIso
      (S1742StrongTransIsoOfHom (F := S1726K) (S1755Lift A B f))
      (S1755BaseChange B).projectionMap.transformation :
      Iso
        (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1726K)
            (S1742HomOfStrongTrans (F := S1726K) (S1755Lift A B f)))
          (S1755BaseChange B).projectionMap.transformation)
        (Pseudofunctor.StrongTrans.vcomp (S1755Lift A B f)
          (S1755BaseChange B).projectionMap.transformation))
    ≪≫ S1755Lift_toY A B f⟩

noncomputable def S1765QuotToOver (A B : S1728Cover) :
    S1756CoverMapQuot A B -> S1762ModelHomOver A B :=
  Quot.lift
    (fun f =>
      { hom := S1755ModelHomOfCoverMap A B f
        overBase := S1765OverBaseOfCoverMap f })
    (by
      intro f g hr
      apply S1762ModelHomOver.ext
      exact S1761LiftWellDefined A B f g hr)

#print axioms S1765QuotToOver

end LeanFormal.IUT.XiFPaper.S1765QuotToOverProbeAdapted
end
