import tmp.sheaf.xif.paper.S2610M2WitnessPartialActual
import tmp.sheaf.xif.paper.S2512StackOpenImmersionUB

/-! # S2611: M2 twoCell_ext actual -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2512StackOpenImmersionUB
open LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal
open LeanFormal.IUT.XiFPaper.S2605M2BaseWitnessActual

namespace LeanFormal.IUT.XiFPaper.S2611M2TwoCellExtActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

theorem twoCell_ext
    {W : EtaleStackPseudofunctor S1726K}
    {first second : Pseudofunctor.StrongTrans W
      (schemeRepresentableEtalePseudofunctor S1726K
        (LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual.S2165Apex
          m s vy Q))}
    (alpha beta : first ⟶ second)
    (h1 : Pseudofunctor.StrongTrans.whiskerRight alpha
      (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
      Pseudofunctor.StrongTrans.whiskerRight beta
        (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX)
    (h2 : Pseudofunctor.StrongTrans.whiskerRight alpha
      (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toY =
      Pseudofunctor.StrongTrans.whiskerRight beta
        (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toY) :
    alpha = beta :=
  (S2512Modification_subsingleton (F := S1726K) first second).elim alpha beta

#check twoCell_ext
#print axioms twoCell_ext

end LeanFormal.IUT.XiFPaper.S2611M2TwoCellExtActual
end
