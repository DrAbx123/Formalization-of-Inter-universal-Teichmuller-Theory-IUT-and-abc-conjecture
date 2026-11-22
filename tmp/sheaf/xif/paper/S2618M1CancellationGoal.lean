import tmp.sheaf.xif.paper.S2617M2StatementActual

/-! # S2618: M1 cancellation exact goals -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual

namespace LeanFormal.IUT.XiFPaper.S2618M1CancellationGoal

universe u

def M1CancellationGoal : Type 1 :=
  ∀ {X Y Z : EtaleStackOverField S1726K}
    (m : X.Hom Y) (y : Y.Hom Z)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber)
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m y) T
      (Pseudofunctor.StrongTrans.vcomp ptY y)),
    Iso (Pseudofunctor.StrongTrans.vcomp Qx.toSource m)
      (Pseudofunctor.StrongTrans.vcomp Qx.projectionMap.transformation ptY)

def M1CancellationWitnessGoal : Type 1 :=
  ∀ {X Y Z : EtaleStackOverField S1726K}
    (m : X.Hom Y) (y : Y.Hom Z)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber)
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m y) T
      (Pseudofunctor.StrongTrans.vcomp ptY y))
    (commutes : Iso (Pseudofunctor.StrongTrans.vcomp Qx.toSource m)
      (Pseudofunctor.StrongTrans.vcomp Qx.projectionMap.transformation ptY)),
    (EtalePseudofunctorSquare.mk
      Qx.toSource Qx.projectionMap.transformation m ptY commutes).TwoPullbackWitness

#check M1CancellationGoal
#check M1CancellationWitnessGoal

end LeanFormal.IUT.XiFPaper.S2618M1CancellationGoal
end
