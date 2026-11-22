import tmp.sheaf.xif.paper.S2609M2SchemeConeMorphismActual
import tmp.sheaf.xif.paper.S2605M2BaseWitnessActual

/-! # S2610: M2WitnessRemaining with actual liftTwoCell -/

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
open LeanFormal.IUT.XiFPaper.S2602M2SchemeWitnessGoal
open LeanFormal.IUT.XiFPaper.S2603M2SchemeWitnessActual
open LeanFormal.IUT.XiFPaper.S2604M2BaseWitnessPartial
open LeanFormal.IUT.XiFPaper.S2605M2BaseWitnessActual
open LeanFormal.IUT.XiFPaper.S2609M2SchemeConeMorphismActual

namespace LeanFormal.IUT.XiFPaper.S2610M2WitnessPartialActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)
noncomputable def P0 : BaseSquareWitnessPartial (m := m) (s := s) (vy := vy) (Q := Q) :=
  partialWitness (m := m) (s := s) (vy := vy) (Q := Q)

noncomputable def liftTwoCell
    {W : EtaleStackPseudofunctor S1726K}
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target) :
    ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).lift source ⟶ (P0 (m := m) (s := s) (vy := vy) (Q := Q)).lift target) :=
  (schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftTwoCell W
    (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) source)
    (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) target)
    (schemeConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f)

noncomputable def remainingOf
    (hX : ∀ (W : EtaleStackPseudofunctor S1726K)
      (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
      (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target),
      Pseudofunctor.StrongTrans.whiskerRight
        (liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f)
        (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
      ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToX source).hom ≫ f.toX ≫ ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToX target).inv)
    (hY : ∀ (W : EtaleStackPseudofunctor S1726K)
      (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
      (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target),
      Pseudofunctor.StrongTrans.whiskerRight
        (liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f)
        (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toY =
      ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToY source).hom ≫ f.toY ≫ ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToY target).inv)
    (hext : ∀ (W : EtaleStackPseudofunctor S1726K)
      {first second : Pseudofunctor.StrongTrans W
        (schemeRepresentableEtalePseudofunctor S1726K
          (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)))}
      (alpha beta : first ⟶ second),
      Pseudofunctor.StrongTrans.whiskerRight alpha
        (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
        Pseudofunctor.StrongTrans.whiskerRight beta
          (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX →
      Pseudofunctor.StrongTrans.whiskerRight alpha
        (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toY =
        Pseudofunctor.StrongTrans.whiskerRight beta
          (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toY →
      alpha = beta) :
    M2WitnessRemaining (m := m) (s := s) (vy := vy) (Q := Q)
      (P0 (m := m) (s := s) (vy := vy) (Q := Q)) where
  liftTwoCell := fun W source target f => liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f
  liftTwoCell_toX := hX
  liftTwoCell_toY := hY
  twoCell_ext := hext

#check liftTwoCell
#check remainingOf
#print axioms remainingOf

end LeanFormal.IUT.XiFPaper.S2610M2WitnessPartialActual
end
