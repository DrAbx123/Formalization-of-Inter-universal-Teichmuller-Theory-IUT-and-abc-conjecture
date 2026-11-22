import tmp.sheaf.xif.paper.S2613C1WhiskerRightCompActual
import tmp.sheaf.xif.paper.S2614WhiskerRightVcompActual

/-! # S2616: outer allocation step of hX (C1/C2) and alignment with P0.liftToX

The target hX (S2612) is

  whiskerRight (liftTwoCell source target f) baseSquare.toX
     = ((P0).liftToX source).hom ≫ f.toX ≫ ((P0).liftToX target).inv.

This file constructs the *outer allocation step* of that proof:

* baseSquare_toX_eq_vcomp (C2a): baseSquare.toX is the composite
  schemeSquare.toX ≫ Q.toSource, definitionally;
* hX_outer (C1/C2): applying whiskerRight_comp (S2613) to the outer
  whiskering gives the associator form
  assoc_inv ≫ whiskerRight (whiskerRight (liftTwoCell f) schemeSquare.toX)
     Q.toSource ≫ assoc_hom;
* hX_inner_schemeSquare (C3): the inner whiskering is computed by the
  schemeWitness.liftTwoCell_toX coherence of S2603/S2605;
* whiskerRight_schemeConeMorphism_toX: the Q.isPullback-level bridge
  replacing the inner schemeConeMorphism two-cell by Q.isPullback.liftTwoCell;
* hX_outer_P0_unfold_hom / hX_outer_P0_unfold_inv: the alignment lemmas,
  expanding (P0).liftToX into exactly the scheme-level pieces produced by the
  outer allocation (associator, schemeWitness.liftToX, Q.isPullback.liftToX);
* hX_outer_aligned: the composite of all of the above, which is precisely the
  hX target of S2612.

No sorry, no axiom, no native_decide.
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
open LeanFormal.IUT.XiFPaper.S2607M2SchemeConeMorphismPartial
open LeanFormal.IUT.XiFPaper.S2608M2QConeMorphismActual
open LeanFormal.IUT.XiFPaper.S2609M2SchemeConeMorphismActual
open LeanFormal.IUT.XiFPaper.S2610M2WitnessPartialActual
open LeanFormal.IUT.XiFPaper.S2613C1WhiskerRightCompActual
open LeanFormal.IUT.XiFPaper.S2614WhiskerRightVcompActual

namespace LeanFormal.IUT.XiFPaper.S2616C1HXOuterActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

/-- C2a: the source leg of baseSquare is the source leg of schemeSquare
composed with Q.toSource, definitionally. -/
theorem baseSquare_toX_eq_vcomp :
    (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
      Pseudofunctor.StrongTrans.vcomp
        (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource := rfl

/-- C1/C2: the outer allocation step of hX.  Rewriting baseSquare.toX as
schemeSquare.toX ≫ Q.toSource and applying whiskerRight_comp (S2613) puts
the outer whiskerRight (liftTwoCell f) baseSquare.toX into the associator
form.  The inner whiskering of liftTwoCell is still present. -/
theorem hX_outer
    (W : EtaleStackPseudofunctor S1726K)
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target) :
    Pseudofunctor.StrongTrans.whiskerRight
      (liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f)
      (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
    (S2058AssociatorIso ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).lift source)
      (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).inv
      ≫ Pseudofunctor.StrongTrans.whiskerRight
          (Pseudofunctor.StrongTrans.whiskerRight
            (liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f)
            (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX) Q.toSource
      ≫ (S2058AssociatorIso ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).lift target)
          (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).hom := by
  rw [baseSquare_toX_eq_vcomp (m := m) (s := s) (vy := vy) (Q := Q)]
  exact whiskerRight_comp_step (m := m) (s := s) (vy := vy) (Q := Q) W
    (liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f)

/-- C3: the inner whiskering of liftTwoCell along schemeSquare.toX is
computed by the schemeWitness.liftTwoCell_toX coherence. -/
theorem hX_inner_schemeSquare
    (W : EtaleStackPseudofunctor S1726K)
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target) :
    Pseudofunctor.StrongTrans.whiskerRight
      (liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f)
      (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
    ((schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftToX W
        (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) source)).hom
      ≫ (schemeConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f).toX
      ≫ ((schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftToX W
        (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) target)).inv := by
  rw [show liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f =
      (schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftTwoCell W
        (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) source)
        (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) target)
        (schemeConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f) from rfl]
  exact (schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftTwoCell_toX W
    (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) source)
    (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) target)
    (schemeConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f)

/-- The Q.isPullback-level bridge: whiskering the schemeConeMorphism two-cell
along Q.toSource is the comparison given by Q.isPullback.liftTwoCell_toX
for the qSquare cone morphism, whose toX component is f.toX. -/
theorem whiskerRight_schemeConeMorphism_toX
    (W : EtaleStackPseudofunctor S1726K)
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target) :
    Pseudofunctor.StrongTrans.whiskerRight
      ((schemeConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f).toX) Q.toSource =
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
  rw [Q.isPullback.liftTwoCell_toX W
    (coneQ (m := m) (s := s) (vy := vy) (Q := Q) source)
    (coneQ (m := m) (s := s) (vy := vy) (Q := Q) target)
    (qConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f)]
  rw [show (qConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f).toX = f.toX from rfl]

/-- Alignment (hom): the hom of P0.liftToX expanded into exactly the
scheme-level pieces produced by the outer allocation: the associator inverse,
the whiskering of schemeWitness.liftToX, and Q.isPullback.liftToX. -/
theorem hX_outer_P0_unfold_hom
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

/-- Alignment (inv): the inv of P0.liftToX expanded into the same
scheme-level pieces, in reverse order. -/
theorem hX_outer_P0_unfold_inv
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
        (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).hom := rfl

/-- The alignment of the outer allocation with P0.liftToX: composing the
outer step, the inner schemeWitness computation, the distribution of the
whiskering, the Q.isPullback bridge and the two P0.liftToX expansions gives
exactly the hX target of S2612. -/
theorem hX_outer_aligned
    (W : EtaleStackPseudofunctor S1726K)
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target) :
    Pseudofunctor.StrongTrans.whiskerRight
      (liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f)
      (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
    ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToX source).hom
      ≫ f.toX
      ≫ ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).liftToX target).inv := by
  rw [hX_outer (m := m) (s := s) (vy := vy) (Q := Q) W source target f]
  rw [hX_inner_schemeSquare (m := m) (s := s) (vy := vy) (Q := Q) W source target f]
  rw [whiskerRight_vcomp (κ := Q.toSource)]
  rw [whiskerRight_vcomp (κ := Q.toSource)]
  rw [whiskerRight_schemeConeMorphism_toX (m := m) (s := s) (vy := vy) (Q := Q) W source target f]
  rw [hX_outer_P0_unfold_hom (m := m) (s := s) (vy := vy) (Q := Q) W source]
  rw [hX_outer_P0_unfold_inv (m := m) (s := s) (vy := vy) (Q := Q) W target]
  simp only [Category.assoc]

#check baseSquare_toX_eq_vcomp
#check hX_outer
#check hX_inner_schemeSquare
#check whiskerRight_schemeConeMorphism_toX
#check hX_outer_P0_unfold_hom
#check hX_outer_P0_unfold_inv
#check hX_outer_aligned

#print axioms baseSquare_toX_eq_vcomp
#print axioms hX_outer
#print axioms hX_inner_schemeSquare
#print axioms whiskerRight_schemeConeMorphism_toX
#print axioms hX_outer_P0_unfold_hom
#print axioms hX_outer_P0_unfold_inv
#print axioms hX_outer_aligned

end LeanFormal.IUT.XiFPaper.S2616C1HXOuterActual
end
