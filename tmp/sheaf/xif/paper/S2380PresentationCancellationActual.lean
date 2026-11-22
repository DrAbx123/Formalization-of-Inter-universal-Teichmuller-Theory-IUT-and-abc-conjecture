import tmp.sheaf.xif.paper.S2377StackPresentationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2089StackCancellationActual
namespace LeanFormal.IUT.XiFPaper.S2380PresentationCancellationActual

universe u

structure S2380PresentationInputs
    {X Y Z : EtaleStackOverField S1726K}
    (f : X.Hom Y) (g : Y.Hom Z) (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber) where
  pointZ : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K T) Z.fiber
  pointZ_eq : pointZ = Pseudofunctor.StrongTrans.vcomp ptY g
  gPresentation : EtaleStackBaseChangePresentation g T pointZ
  fgPresentation : EtaleStackBaseChangePresentation
    (Pseudofunctor.StrongTrans.vcomp f g) T pointZ
  cancel : forall {a b : X.Hom Y},
    Iso (Pseudofunctor.StrongTrans.vcomp a g)
      (Pseudofunctor.StrongTrans.vcomp b g) ->
    Iso a b

def S2380ConstructFPresentation : Type 1 :=
  forall {X Y Z : EtaleStackOverField S1726K}
    (f : X.Hom Y) (g : Y.Hom Z) (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber),
    S2380PresentationInputs f g T ptY ->
      EtaleStackBaseChangePresentation f T ptY

structure S2380PostcompSupply : Type 1 where
  cancel : forall {X Y Z : EtaleStackOverField S1726K} (g : Y.Hom Z)
    {a b : X.Hom Y},
    Iso (Pseudofunctor.StrongTrans.vcomp a g)
      (Pseudofunctor.StrongTrans.vcomp b g) ->
    Iso a b

noncomputable def S2380StackPresentationStatementOfConstruction
    (h : S2380ConstructFPresentation) (pc : S2380PostcompSupply) :
    S2089StackPresentationStatement := by
  intro X Y Z f g hfg hg T ptY
  let pointZ : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Z.fiber :=
    Pseudofunctor.StrongTrans.vcomp ptY g
  let gPres : EtaleStackBaseChangePresentation g T pointZ :=
    hg.baseChange T pointZ
  let fgPres : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp f g) T pointZ :=
    hfg.baseChange T pointZ
  exact h f g T ptY
    { pointZ := pointZ
      pointZ_eq := rfl
      gPresentation := gPres
      fgPresentation := fgPres
      cancel := pc.cancel g }

def S2380PresentationFirstMissing : Prop :=
  Nonempty S2380ConstructFPresentation

theorem S2380PresentationFirstMissing_iff :
    S2380PresentationFirstMissing ↔
      Nonempty S2380ConstructFPresentation :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2380PresentationCancellationActual
end