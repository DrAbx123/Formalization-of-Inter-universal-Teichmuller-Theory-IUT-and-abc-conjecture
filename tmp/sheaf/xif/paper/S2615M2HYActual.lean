import tmp.sheaf.xif.paper._M2HXFinalAgent
import tmp.sheaf.xif.paper.S2611M2TwoCellExtActual

/-! # S2615: hY actual (mirror of hX, simpler because liftToY is schemeWitness.liftToY) -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal
open LeanFormal.IUT.XiFPaper.S2602M2SchemeWitnessGoal
open LeanFormal.IUT.XiFPaper.S2603M2SchemeWitnessActual
open LeanFormal.IUT.XiFPaper.S2604M2BaseWitnessPartial
open LeanFormal.IUT.XiFPaper.S2605M2BaseWitnessActual
open LeanFormal.IUT.XiFPaper.S2607M2SchemeConeMorphismPartial
open LeanFormal.IUT.XiFPaper.S2608M2QConeMorphismActual
open LeanFormal.IUT.XiFPaper.S2609M2SchemeConeMorphismActual
open LeanFormal.IUT.XiFPaper.S2610M2WitnessPartialActual
open LeanFormal.IUT.XiFPaper.S2611M2TwoCellExtActual

namespace LeanFormal.IUT.XiFPaper.S2615M2HYActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

theorem hY
    (W : EtaleStackPseudofunctor S1726K)
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target) :
    Pseudofunctor.StrongTrans.whiskerRight
      (liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f)
      (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toY =
    ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToY source).hom
      ≫ f.toY
      ≫ ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToY target).inv := by
  change Pseudofunctor.StrongTrans.whiskerRight
      ((schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftTwoCell W
        (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) source)
        (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) target)
        (schemeConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f))
      (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toY =
    ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToY source).hom
      ≫ f.toY
      ≫ ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToY target).inv
  rw [(schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftTwoCell_toY W
    (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) source)
    (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) target)
    (schemeConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f)]
  rfl

#check hY
#print axioms hY

end LeanFormal.IUT.XiFPaper.S2615M2HYActual
end
