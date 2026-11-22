import tmp.sheaf.xif.paper.S1768CommutesActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756QuotientActual
open LeanFormal.IUT.XiFPaper.S1761SubsingletonIsoActual
open LeanFormal.IUT.XiFPaper.S1762OverModelHomActual
open LeanFormal.IUT.XiFPaper.S1766WhiskerBridgeActual
open LeanFormal.IUT.XiFPaper.S1767OverToQuotConditionalActual
open LeanFormal.IUT.XiFPaper.S1768CommutesActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1771OverEquivProgress

variable {A B : S1728Cover}

theorem S1771_candidate_iso (f : S1728CoverMap A B) :
    Nonempty (Iso
      (S1767CandidateMap (S1766QuotToOver A B (Quot.mk (fun f g : S1728CoverMap A B => S1728CoverMapRel f g) f)))
      f.map) := by
  let g0 : S1762ModelHomOver A B :=
    { hom := S1755ModelHomOfCoverMap A B f
      overBase := S1766OverBaseOfCoverMap f }
  change Nonempty (Iso (S1767CandidateMap g0) f.map)
  dsimp [S1767CandidateMap]
  refine ⟨?_⟩
  let sec := S1755ModelSectionLift A
  let a := (S1755BaseChange A).toSource
  let tB := (S1755BaseChange B).toSource
  let G : Pseudofunctor.StrongTrans (S1755ModelStack A) (S1755ModelStack B) :=
    S1742StrongTransOfHom (F := S1726K)
      (S1755ModelHomOfCoverMap A B f)
  let Lf := S1755Lift A B f
  let eG : Iso G Lf :=
    S1742StrongTransIsoOfHom (F := S1726K) (S1755Lift A B f)
  let e1 : Iso (Pseudofunctor.StrongTrans.vcomp sec
      (Pseudofunctor.StrongTrans.vcomp G tB))
      (Pseudofunctor.StrongTrans.vcomp sec
      (Pseudofunctor.StrongTrans.vcomp Lf tB)) :=
    S1768whiskerLeftV sec (S1768whiskerRightV eG tB)
  let e2 : Iso (Pseudofunctor.StrongTrans.vcomp sec
      (Pseudofunctor.StrongTrans.vcomp Lf tB))
      (Pseudofunctor.StrongTrans.vcomp sec
      (Pseudofunctor.StrongTrans.vcomp a f.map)) :=
    S1768whiskerLeftV sec (S1755Lift_toX A B f)
  let e3 : Iso (Pseudofunctor.StrongTrans.vcomp sec
      (Pseudofunctor.StrongTrans.vcomp a f.map)) f.map :=
    (S1768assocV sec a f.map).symm ≪≫
      S1768whiskerRightV (S1755ModelSection A) f.map ≪≫
      S1768leftUnitorV f.map
  exact e1 ≪≫ e2 ≪≫ e3

theorem S1771_left_inv (f : S1728CoverMap A B) :
    S1768OverToQuot (S1766QuotToOver A B (Quot.mk (fun f g : S1728CoverMap A B => S1728CoverMapRel f g) f))
      = Quot.mk (fun f g : S1728CoverMap A B => S1728CoverMapRel f g) f := by
  apply Quot.sound
  let g0 : S1762ModelHomOver A B :=
    { hom := S1755ModelHomOfCoverMap A B f
      overBase := S1766OverBaseOfCoverMap f }
  change S1728CoverMapRel
    { map := S1767CandidateMap g0
      commutes := (S1768Commutes g0).commutes } f
  exact S1771_candidate_iso f

#check S1771_candidate_iso
#check S1771_left_inv
#print axioms S1771_left_inv
end LeanFormal.IUT.XiFPaper.S1771OverEquivProgress
end
