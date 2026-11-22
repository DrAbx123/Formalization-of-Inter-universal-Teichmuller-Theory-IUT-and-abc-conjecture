import tmp.sheaf.xif.paper.S2605M2BaseWitnessActual

/-! # S2606: exact liftTwoCell_toX/toY subgoals -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2604M2BaseWitnessPartial
open LeanFormal.IUT.XiFPaper.S2605M2BaseWitnessActual

namespace LeanFormal.IUT.XiFPaper.S2606LiftTwoCellGoal

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)
variable (P : BaseSquareWitnessPartial (m := m) (s := s) (vy := vy) (Q := Q))

abbrev BaseSquare := baseSquare (m := m) (s := s) (vy := vy) (Q := Q)

def LiftTwoCellCandidate : Type 1 :=
  ∀ (W : EtaleStackPseudofunctor S1726K)
    (source target : (BaseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W),
    (BaseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target →
    (P.lift source ⟶ P.lift target)

def LiftTwoCellToXStatement
    (lt : LiftTwoCellCandidate (m := m) (s := s) (vy := vy) (Q := Q) P) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K)
    (source target : (BaseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (BaseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target),
    Pseudofunctor.StrongTrans.whiskerRight (lt W source target f)
        (BaseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
      (P.liftToX source).hom ≫ f.toX ≫ (P.liftToX target).inv

def LiftTwoCellToYStatement
    (lt : LiftTwoCellCandidate (m := m) (s := s) (vy := vy) (Q := Q) P) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K)
    (source target : (BaseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (BaseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target),
    Pseudofunctor.StrongTrans.whiskerRight (lt W source target f)
        (BaseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toY =
      (P.liftToY source).hom ≫ f.toY ≫ (P.liftToY target).inv

#check LiftTwoCellCandidate
#check LiftTwoCellToXStatement
#check LiftTwoCellToYStatement

end LeanFormal.IUT.XiFPaper.S2606LiftTwoCellGoal
end
