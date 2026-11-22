import tmp.sheaf.xif.paper.S2603M2SchemeWitnessActual
import tmp.sheaf.xif.paper.S2601M2WitnessGoal
import tmp.sheaf.xif.paper.S2058D6FiniteEtaleActual

/-! # S2604: partial base-change witness for M2 -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2175BaseChangePresentationActual
open LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal
open LeanFormal.IUT.XiFPaper.S2602M2SchemeWitnessGoal
open LeanFormal.IUT.XiFPaper.S2603M2SchemeWitnessActual

namespace LeanFormal.IUT.XiFPaper.S2604M2BaseWitnessPartial

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

noncomputable def qSquare : EtalePseudofunctorSquare
    (schemeRepresentableEtalePseudofunctor S1726K Q.pullbackScheme)
    X.fiber
    (schemeRepresentableEtalePseudofunctor S1726K A)
    Y.fiber where
  toX := Q.toSource
  toY := Q.projectionMap.transformation
  xToBase := m
  yToBase := vy
  commutes := Q.commutes

noncomputable def coneQ {W : EtaleStackPseudofunctor S1726K}
    (c : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W) :
    (qSquare (m := m) (vy := vy) (Q := Q)).Cone W where
  toX := c.toX
  toY := Pseudofunctor.StrongTrans.vcomp c.toY (S1742StrongTransOfHom s)
  commutes := c.commutes.trans
    (S2058AssociatorIso c.toY (S1742StrongTransOfHom s) vy).symm

noncomputable def schemeCone {W : EtaleStackPseudofunctor S1726K}
    (c : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W) :
    (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W where
  toX := Q.isPullback.lift W (coneQ (m := m) (s := s) (vy := vy) (Q := Q) c)
  toY := c.toY
  commutes := Q.isPullback.liftToY W
    (coneQ (m := m) (s := s) (vy := vy) (Q := Q) c)

noncomputable def vertexLift {W : EtaleStackPseudofunctor S1726K}
    (c : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W) :
    Pseudofunctor.StrongTrans W
      (schemeRepresentableEtalePseudofunctor S1726K
        (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q))) :=
  schemeWitness (m := m) (s := s) (vy := vy) (Q := Q) |>.lift W
    (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) c)

structure BaseSquareWitnessPartial where
  lift : ∀ {W : EtaleStackPseudofunctor S1726K},
    (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W →
    Pseudofunctor.StrongTrans W
      (schemeRepresentableEtalePseudofunctor S1726K
        (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)))
  liftToX : ∀ {W} (c : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W),
    Iso (Pseudofunctor.StrongTrans.vcomp (lift c)
      (S2175ToSource (m := m) (s := s) (vy := vy) (Q := Q))) c.toX
  liftToY : ∀ {W} (c : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W),
    Iso (Pseudofunctor.StrongTrans.vcomp (lift c)
      (S1742StrongTransOfHom (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)))) c.toY

noncomputable def partialWitness :
    BaseSquareWitnessPartial (m := m) (s := s) (vy := vy) (Q := Q) where
  lift := fun {W} c => vertexLift (m := m) (s := s) (vy := vy) (Q := Q) c
  liftToX := by
    intro W c
    have hXdef : (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
        S1742StrongTransOfHom (S2165Fst (m := m) (s := s) (vy := vy) (Q := Q)) := rfl
    have hliftdef : (schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).lift W
        (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) c) =
        vertexLift (m := m) (s := s) (vy := vy) (Q := Q) c := rfl
    have hwx0 := (schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftToX W
      (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) c)
    rw [hXdef] at hwx0
    rw [hliftdef] at hwx0
    exact (S2058AssociatorIso (vertexLift (m := m) (s := s) (vy := vy) (Q := Q) c)
        (S1742StrongTransOfHom (S2165Fst (m := m) (s := s) (vy := vy) (Q := Q)))
        Q.toSource).symm.trans
      ((S2058WhiskerRightIso _ _ Q.toSource hwx0).trans
        (Q.isPullback.liftToX W
          (coneQ (m := m) (s := s) (vy := vy) (Q := Q) c)))
  liftToY := by
    intro W c
    exact (schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftToY W
      (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) c)

#check partialWitness
#print axioms partialWitness

end LeanFormal.IUT.XiFPaper.S2604M2BaseWitnessPartial
end
