import tmp.sheaf.xif.paper.S2618M1CancellationGoal
import tmp.sheaf.xif.paper.S2058D6FiniteEtaleActual

/-! # S2619: right cancellation data and M1 cancellation reduction -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2618M1CancellationGoal

namespace LeanFormal.IUT.XiFPaper.S2619RightCancellationActual

universe u

/-- The missing coherence: right whiskering by `y` is conservative on
2-isomorphisms. -/
structure RightCancellation {Y Z : EtaleStackOverField S1726K} (y : Y.Hom Z) : Type 1 where
  cancelRight : ∀ {P : EtaleStackPseudofunctor S1726K}
    (A B : Pseudofunctor.StrongTrans P Y.fiber),
    Iso (Pseudofunctor.StrongTrans.vcomp A y)
      (Pseudofunctor.StrongTrans.vcomp B y) →
    Iso A B

noncomputable def cancellationOf
    {X Y Z : EtaleStackOverField S1726K} (m : X.Hom Y) (y : Y.Hom Z)
    (R : RightCancellation y)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber)
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m y) T
      (Pseudofunctor.StrongTrans.vcomp ptY y)) :
    Iso (Pseudofunctor.StrongTrans.vcomp Qx.toSource m)
      (Pseudofunctor.StrongTrans.vcomp Qx.projectionMap.transformation ptY) :=
  R.cancelRight
    (Pseudofunctor.StrongTrans.vcomp Qx.toSource m)
    (Pseudofunctor.StrongTrans.vcomp Qx.projectionMap.transformation ptY)
    ((S2058AssociatorIso Qx.toSource m y).trans
      (Qx.commutes.trans
        (S2058AssociatorIso Qx.projectionMap.transformation ptY y).symm))

#check cancellationOf
#print axioms cancellationOf

end LeanFormal.IUT.XiFPaper.S2619RightCancellationActual
end
