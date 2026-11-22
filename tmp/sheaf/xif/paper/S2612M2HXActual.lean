import tmp.sheaf.xif.paper.S2610M2WitnessPartialActual
import tmp.sheaf.xif.paper.S2611M2TwoCellExtActual

/-! # S2612: hX attempt via whiskerRight_comp + liftTwoCell_toX -/

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
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal
open LeanFormal.IUT.XiFPaper.S2602M2SchemeWitnessGoal
open LeanFormal.IUT.XiFPaper.S2603M2SchemeWitnessActual
open LeanFormal.IUT.XiFPaper.S2604M2BaseWitnessPartial
open LeanFormal.IUT.XiFPaper.S2605M2BaseWitnessActual
open LeanFormal.IUT.XiFPaper.S2609M2SchemeConeMorphismActual
open LeanFormal.IUT.XiFPaper.S2610M2WitnessPartialActual

namespace LeanFormal.IUT.XiFPaper.S2612M2HXActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

theorem hX
    (W : EtaleStackPseudofunctor S1726K)
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target) :
    Pseudofunctor.StrongTrans.whiskerRight
      (liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f)
      (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
    ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToX source).hom
      ≫ f.toX
      ≫ ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToX target).inv := by
  simp only [liftTwoCell, schemeConeMorphism, schemeConeMorphismOf,
    P0, partialWitness, vertexLift, schemeCone, coneQ,
    Q.isPullback.liftTwoCell_toX, schemeWitness.liftTwoCell_toX,
    Iso.trans_hom, Category.assoc]

#check hX
#print axioms hX

end LeanFormal.IUT.XiFPaper.S2612M2HXActual
end
