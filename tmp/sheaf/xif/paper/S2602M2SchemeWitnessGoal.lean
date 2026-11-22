import tmp.sheaf.xif.paper.S2601M2WitnessGoal
import tmp.sheaf.xif.paper.S2175BaseChangePresentationActual

/-! # S2602: scheme-level pullback witness subgoal for M2 -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2175BaseChangePresentationActual

namespace LeanFormal.IUT.XiFPaper.S2602M2SchemeWitnessGoal

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

/-- The scheme-level pullback square of `S2165Fst`/`S2165Snd`. -/
noncomputable def schemeSquare : EtalePseudofunctorSquare
    (schemeRepresentableEtalePseudofunctor S1726K
      (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)))
    (schemeRepresentableEtalePseudofunctor S1726K Q.pullbackScheme)
    (schemeRepresentableEtalePseudofunctor S1726K T)
    (schemeRepresentableEtalePseudofunctor S1726K A) where
  toX := S1742StrongTransOfHom (S2165Fst (m := m) (s := s) (vy := vy) (Q := Q))
  toY := S1742StrongTransOfHom (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q))
  xToBase := Q.projectionMap.transformation
  yToBase := S1742StrongTransOfHom s
  commutes := S2175ProjectionIso (m := m) (s := s) (vy := vy) (Q := Q)

/-- Exact scheme-level pullback witness still needed. -/
def SchemePullbackWitnessRequired : Type 1 :=
  (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).TwoPullbackWitness

#check schemeSquare
#check SchemePullbackWitnessRequired

end LeanFormal.IUT.XiFPaper.S2602M2SchemeWitnessGoal
end
