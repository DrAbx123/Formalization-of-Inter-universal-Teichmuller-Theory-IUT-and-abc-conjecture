import tmp.sheaf.xif.paper._M2HXFinalAgent
import tmp.sheaf.xif.paper.S2615M2HYActual
import tmp.sheaf.xif.paper.S2611M2TwoCellExtActual
import tmp.sheaf.xif.paper.S2605M2BaseWitnessActual
import tmp.sheaf.xif.paper.S2601M2WitnessGoal

/-! # S2616: full M2 base witness actual -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal
open LeanFormal.IUT.XiFPaper.S2605M2BaseWitnessActual
open LeanFormal.IUT.XiFPaper.S2610M2WitnessPartialActual
open LeanFormal.IUT.XiFPaper.M2HXFinalAgent
open LeanFormal.IUT.XiFPaper.S2615M2HYActual
open LeanFormal.IUT.XiFPaper.S2611M2TwoCellExtActual

namespace LeanFormal.IUT.XiFPaper.S2616M2FullWitnessActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

noncomputable def m2Witness :
    M2TwoPullbackRequired (m := m) (s := s) (vy := vy) (Q := Q) :=
  fullWitness (m := m) (s := s) (vy := vy) (Q := Q)
    (P0 (m := m) (s := s) (vy := vy) (Q := Q))
    (remainingOf (m := m) (s := s) (vy := vy) (Q := Q)
      (hX (m := m) (s := s) (vy := vy) (Q := Q))
      (hY (m := m) (s := s) (vy := vy) (Q := Q))
      (fun W first second alpha beta h1 h2 =>
        twoCell_ext (m := m) (s := s) (vy := vy) (Q := Q)
          (W := W) (first := first) (second := second) alpha beta h1 h2))

noncomputable def m2Presentation :
    EtaleStackBaseChangePresentation m T
      (LeanFormal.IUT.XiFPaper.S2600M2CommutesActual.basePoint s vy) :=
  presentationOfWitness m s vy Q
    (m2Witness (m := m) (s := s) (vy := vy) (Q := Q))

#check m2Witness
#check m2Presentation
#print axioms m2Witness
#print axioms m2Presentation

end LeanFormal.IUT.XiFPaper.S2616M2FullWitnessActual
end
