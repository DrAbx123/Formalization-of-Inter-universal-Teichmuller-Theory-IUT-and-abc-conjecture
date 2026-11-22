import tmp.sheaf.xif.paper.S2613C1WhiskerRightCompActual
import tmp.sheaf.xif.paper.S2611M2TwoCellExtActual

/-! # M2 hX, steps C2/C3 (agent)

Target: the first two reductions of `hX` in S2612.

* C2: `(baseSquare ...).toX = (schemeSquare ...).toX ≫ Q.toSource`
  definitionally, then `whiskerRight_comp_step` (S2613).
* C3: eliminate the inner `whiskerRight` of `liftTwoCell` by the
  `(schemeWitness ...).liftTwoCell_toX` projection of S2603/S2605.

No sorry, no native_decide.
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

namespace LeanFormal.IUT.XiFPaper.M2HXC2C3Agent

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

/-- C2a: the source leg of `baseSquare` is the composite of the source leg of
`schemeSquare` with `Q.toSource`, definitionally. -/
theorem baseSquare_toX_vcomp :
    (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
      Pseudofunctor.StrongTrans.vcomp
        (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX
        Q.toSource := rfl

/-- C2: rewrite the outer `whiskerRight` along the decomposition of
`baseSquare.toX` by `whiskerRight_comp_step` (S2613).  The inner
`whiskerRight` of the lift two-cell is still present. -/
theorem hX_step1
    {W : EtaleStackPseudofunctor S1726K}
    {f f' : Pseudofunctor.StrongTrans W
      (schemeRepresentableEtalePseudofunctor S1726K
        (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)))}
    (L : f ⟶ f') :
    Pseudofunctor.StrongTrans.whiskerRight L
      (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
    (S2058AssociatorIso f
      (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).inv
      ≫ Pseudofunctor.StrongTrans.whiskerRight
          (Pseudofunctor.StrongTrans.whiskerRight L
            (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX) Q.toSource
      ≫ (S2058AssociatorIso f'
          (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).hom := by
  change Pseudofunctor.StrongTrans.whiskerRight L
      (Pseudofunctor.StrongTrans.vcomp
        (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource) =
    (S2058AssociatorIso f
      (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).inv
      ≫ Pseudofunctor.StrongTrans.whiskerRight
          (Pseudofunctor.StrongTrans.whiskerRight L
            (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX) Q.toSource
      ≫ (S2058AssociatorIso f'
          (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).hom
  exact whiskerRight_comp_step (m := m) (s := s) (vy := vy) (Q := Q) W L

/-- C3: eliminate the inner `whiskerRight` of `liftTwoCell` using the
`schemeWitness.liftTwoCell_toX` projection term.  This is the exact
intermediate state of `hX` after the first two reductions. -/
theorem hX_step2
    (W : EtaleStackPseudofunctor S1726K)
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target) :
    Pseudofunctor.StrongTrans.whiskerRight
      (liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f)
      (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX =
    (S2058AssociatorIso ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).lift source)
      (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).inv
      ≫ Pseudofunctor.StrongTrans.whiskerRight
          (((schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftToX W
              (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) source)).hom
            ≫ (schemeConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f).toX
            ≫ ((schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftToX W
                (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) target)).inv)
          Q.toSource
      ≫ (S2058AssociatorIso ((P0 (m := m) (s := s) (vy := vy) (Q := Q)).lift target)
          (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).hom := by
  rw [hX_step1 (m := m) (s := s) (vy := vy) (Q := Q)
    (W := W)
    (f := (P0 (m := m) (s := s) (vy := vy) (Q := Q)).lift source)
    (f' := (P0 (m := m) (s := s) (vy := vy) (Q := Q)).lift target)
    (L := liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f)]
  rw [show liftTwoCell (m := m) (s := s) (vy := vy) (Q := Q) source target f =
      (schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftTwoCell W
        (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) source)
        (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) target)
        (schemeConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f) from rfl]
  rw [(schemeWitness (m := m) (s := s) (vy := vy) (Q := Q)).liftTwoCell_toX W
    (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) source)
    (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) target)
    (schemeConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f)]

#check baseSquare_toX_vcomp
#check hX_step1
#check hX_step2
#print axioms baseSquare_toX_vcomp
#print axioms hX_step1
#print axioms hX_step2

end LeanFormal.IUT.XiFPaper.M2HXC2C3Agent
end