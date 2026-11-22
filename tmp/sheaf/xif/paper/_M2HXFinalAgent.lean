import tmp.sheaf.xif.paper._M2HXC2C3Agent
import tmp.sheaf.xif.paper.S2614WhiskerRightVcompActual

/-! # M2 hX: final step (agent)

Module tmp.sheaf.xif.paper._M2HXC2C3Agent reduces hX (S2610/S2612) to
hX_step2:

  A_s.inv ≫ whiskerRight (h_s ≫ scm.toX ≫ h_t.inv) Q.toSource ≫ A_t.hom
    = (P0.liftToX source).hom ≫ f.toX ≫ (P0.liftToX target).inv,

where h_s/h_t are the two schemeWitness.liftToX comparisons and
scm = schemeConeMorphism f.

This file finishes that goal:

* whiskerRight_vcomp (S2614) distributes the outer whiskerRight over
  h_s, scm.toX and h_t.inv;
* scm.toX = Q.isPullback.liftTwoCell definitionally, so the projection
  Q.isPullback.liftTwoCell_toX replaces it by
  Q.liftToX source ≫ f.toX ≫ Q.liftToX target.inv;
* P0.liftToX (hom and inverse) is unfolded into its associator, whisker and
  Q.liftToX factors, and the two sides become the same composite read with
  different associativity, closed by Category.assoc.

No sorry, no native_decide, no extra axiom.
-/

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
open LeanFormal.IUT.XiFPaper.S2613C1WhiskerRightCompActual
open LeanFormal.IUT.XiFPaper.S2614WhiskerRightVcompActual
open LeanFormal.IUT.XiFPaper.M2HXC2C3Agent

namespace LeanFormal.IUT.XiFPaper.M2HXFinalAgent

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

/-- The hom of the base-square lift comparison P0.liftToX, displayed as
associator inverse, whiskered scheme comparison, and Q-level comparison. -/
theorem liftToX_hom
    (W : EtaleStackPseudofunctor S1726K)
    (c : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W) :
    ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToX c).hom =
      (S2058AssociatorIso ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).lift c)
        (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).inv
      ≫ Pseudofunctor.StrongTrans.whiskerRight
          ((schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftToX W
            (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) c)).hom
          Q.toSource
      ≫ (Q.isPullback.liftToX W
          (coneQ (m := m) (s := s) (vy := vy) (Q := Q) c)).hom := rfl

/-- The inverse of the base-square lift comparison P0.liftToX, displayed in
the reversed factor order. -/
theorem liftToX_inv
    (W : EtaleStackPseudofunctor S1726K)
    (c : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W) :
    ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToX c).inv =
      (Q.isPullback.liftToX W
        (coneQ (m := m) (s := s) (vy := vy) (Q := Q) c)).inv
      ≫ Pseudofunctor.StrongTrans.whiskerRight
          ((schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftToX W
            (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) c)).inv
          Q.toSource
      ≫ (S2058AssociatorIso ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).lift c)
          (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).hom := by
  have hdef : (P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToX c =
      (S2058AssociatorIso ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).lift c)
        (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).symm
      ≪≫ (S2058WhiskerRightIso _ _ Q.toSource
            ((schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftToX W
              (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) c)))
      ≪≫ (Q.isPullback.liftToX W
            (coneQ (m := m) (s := s) (vy := vy) (Q := Q) c)) := rfl
  rw [hdef]
  rw [Iso.trans_inv, Iso.trans_inv, Iso.symm_inv]
  rw [Category.assoc]
  rfl

/-- The projection property of scm.toX = Q.isPullback.liftTwoCell. -/
theorem schemeConeMorphism_toX_proj
    (W : EtaleStackPseudofunctor S1726K)
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target) :
    Pseudofunctor.StrongTrans.whiskerRight
      ((schemeConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f).toX)
      Q.toSource =
    (Q.isPullback.liftToX W
      (coneQ (m := m) (s := s) (vy := vy) (Q := Q) source)).hom
      ≫ f.toX
      ≫ (Q.isPullback.liftToX W
          (coneQ (m := m) (s := s) (vy := vy) (Q := Q) target)).inv := by
  rw [show (schemeConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f).toX =
      Q.isPullback.liftTwoCell W
        (coneQ (m := m) (s := s) (vy := vy) (Q := Q) source)
        (coneQ (m := m) (s := s) (vy := vy) (Q := Q) target)
        (qConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f) from rfl]
  exact Q.isPullback.liftTwoCell_toX W
    (coneQ (m := m) (s := s) (vy := vy) (Q := Q) source)
    (coneQ (m := m) (s := s) (vy := vy) (Q := Q) target)
    (qConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f)

/-- Final step of hX (S2610/S2612): the liftTwoCell_toX coherence for the
base square. -/
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
  rw [hX_step2 (m := m) (s := s) (vy := vy) (Q := Q) W source target f]
  rw [whiskerRight_vcomp]
  rw [whiskerRight_vcomp]
  rw [schemeConeMorphism_toX_proj (m := m) (s := s) (vy := vy) (Q := Q) W source target f]
  rw [liftToX_hom]
  rw [liftToX_inv]
  simp only [Category.assoc]

#check liftToX_hom
#check liftToX_inv
#check schemeConeMorphism_toX_proj
#check hX
#print axioms liftToX_hom
#print axioms liftToX_inv
#print axioms schemeConeMorphism_toX_proj
#print axioms hX

end LeanFormal.IUT.XiFPaper.M2HXFinalAgent
end
