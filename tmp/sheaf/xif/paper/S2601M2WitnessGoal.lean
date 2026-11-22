import tmp.sheaf.xif.paper.S2600M2CommutesActual

/-! # S2601: exact M2 two-pullback goal and conditional presentation -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2175BaseChangePresentationActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2224BaseChangeCommutesFinalActual
open LeanFormal.IUT.XiFPaper.S2600M2CommutesActual

namespace LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

/-- The base-changed 2-commutative square. -/
noncomputable def baseSquare : EtalePseudofunctorSquare
    (schemeRepresentableEtalePseudofunctor S1726K
      (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)))
    X.fiber
    (schemeRepresentableEtalePseudofunctor S1726K T)
    Y.fiber where
  toX := S2175ToSource (m := m) (s := s) (vy := vy) (Q := Q)
  toY := S1742StrongTransOfHom (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q))
  xToBase := m
  yToBase := basePoint (s := s) vy
  commutes := S2224Commutes (m := m) (s := s) (vy := vy) (Q := Q)

/-- Exact remaining M2 witness. -/
def M2TwoPullbackRequired : Type 1 :=
  (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).TwoPullbackWitness

/-- The missing witness gives the base-changed presentation. -/
noncomputable def presentationOfWitness
    (h : M2TwoPullbackRequired (m := m) (s := s) (vy := vy) (Q := Q)) :
    EtaleStackBaseChangePresentation m T
      (basePoint (s := s) vy) where
  pullbackScheme := S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)
  projection := S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)
  projectionMap := projectionMap (m := m) (s := s) (vy := vy) (Q := Q)
  toSource := S2175ToSource (m := m) (s := s) (vy := vy) (Q := Q)
  commutes := S2224Commutes (m := m) (s := s) (vy := vy) (Q := Q)
  isPullback := h

#check M2TwoPullbackRequired
#check presentationOfWitness
#print axioms presentationOfWitness

end LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal
end
