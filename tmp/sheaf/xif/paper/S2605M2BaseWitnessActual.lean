import tmp.sheaf.xif.paper.S2604M2BaseWitnessPartial
import tmp.sheaf.xif.paper.S2601M2WitnessGoal

/-! # S2605: exact remaining M2 base-witness coherence fields -/

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
open LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal
open LeanFormal.IUT.XiFPaper.S2604M2BaseWitnessPartial

namespace LeanFormal.IUT.XiFPaper.S2605M2BaseWitnessActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

variable (P : BaseSquareWitnessPartial (m := m) (s := s) (vy := vy) (Q := Q))

/-- Exact coherence fields still needed for the full base witness. -/
structure M2WitnessRemaining where
  liftTwoCell : ∀ (W : EtaleStackPseudofunctor S1726K)
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W),
    (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target →
    (P.lift source ⟶ P.lift target)
  liftTwoCell_toX : ∀ (W : EtaleStackPseudofunctor S1726K)
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target),
    Pseudofunctor.StrongTrans.whiskerRight (liftTwoCell W source target f)
        (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
      (P.liftToX source).hom ≫ f.toX ≫ (P.liftToX target).inv
  liftTwoCell_toY : ∀ (W : EtaleStackPseudofunctor S1726K)
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target),
    Pseudofunctor.StrongTrans.whiskerRight (liftTwoCell W source target f)
        (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toY =
      (P.liftToY source).hom ≫ f.toY ≫ (P.liftToY target).inv
  twoCell_ext : ∀ (W : EtaleStackPseudofunctor S1726K)
    {first second : Pseudofunctor.StrongTrans W
      (schemeRepresentableEtalePseudofunctor S1726K
        (S2165Apex m s vy Q))}
    (alpha beta : first ⟶ second),
    Pseudofunctor.StrongTrans.whiskerRight alpha
        (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
      Pseudofunctor.StrongTrans.whiskerRight beta
        (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX →
    Pseudofunctor.StrongTrans.whiskerRight alpha
        (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toY =
      Pseudofunctor.StrongTrans.whiskerRight beta
        (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toY →
    alpha = beta

/-- The remaining coherence fields fill the full base witness. -/
noncomputable def fullWitness
    (R : M2WitnessRemaining m s vy Q P) :
    M2TwoPullbackRequired m s vy Q where
  lift := fun W c => P.lift c
  liftToX := fun W c => P.liftToX c
  liftToY := fun W c => P.liftToY c
  liftTwoCell := R.liftTwoCell
  liftTwoCell_toX := R.liftTwoCell_toX
  liftTwoCell_toY := R.liftTwoCell_toY
  twoCell_ext := R.twoCell_ext

#check M2WitnessRemaining
#check fullWitness
#print axioms fullWitness

end LeanFormal.IUT.XiFPaper.S2605M2BaseWitnessActual
end
