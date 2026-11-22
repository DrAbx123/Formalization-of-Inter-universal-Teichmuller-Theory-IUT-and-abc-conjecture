import tmp.sheaf.xif.paper.S2602M2SchemeWitnessGoal
import tmp.sheaf.xif.paper.S2512StackOpenImmersionUB

/-! # S2603: schemeSquare TwoPullbackWitness from S2512Witness -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2175BaseChangePresentationActual
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual
open LeanFormal.IUT.XiFPaper.S2512StackOpenImmersionUB
open LeanFormal.IUT.XiFPaper.S2602M2SchemeWitnessGoal

namespace LeanFormal.IUT.XiFPaper.S2603M2SchemeWitnessActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

noncomputable def schemeWitness :
    SchemePullbackWitnessRequired (m := m) (s := s) (vy := vy) (Q := Q) := by
  have hpb0 : IsPullback
      (S2165Fst (m := m) (s := s) (vy := vy) (Q := Q)).left
      (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)).left
      Q.projection.left s.left := by
    exact IsPullback.of_hasPullback Q.projection.left s.left
  have hF : S2512BaseF (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)) =
      Q.projection := by
    unfold S2512BaseF schemeSquare
    exact S2096HomOfSchemeRepresentableMap Q.projection Q.projectionMap
  have hG : S2512BaseG (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)) = s := by
    unfold S2512BaseG schemeSquare
    exact S1742HomOfStrongTrans_strongTransOfHom s
  have hpb : IsPullback
      (S2165Fst (m := m) (s := s) (vy := vy) (Q := Q)).left
      (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)).left
      (S2512BaseF (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q))).left
      (S2512BaseG (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q))).left := by
    simpa [hF, hG] using hpb0
  exact S2512Witness (pX := S2165Fst (m := m) (s := s) (vy := vy) (Q := Q))
    (pY := S2165Snd (m := m) (s := s) (vy := vy) (Q := Q))
    (sq := schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)) hpb rfl rfl

#check schemeWitness
#print axioms schemeWitness

end LeanFormal.IUT.XiFPaper.S2603M2SchemeWitnessActual
end
