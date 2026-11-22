import tmp.sheaf.xif.paper.S2608M2QConeMorphismActual
import tmp.sheaf.xif.paper.S2610M2WitnessPartialActual
import tmp.sheaf.xif.paper.S2611M2TwoCellExtActual

/-! # S2615: qSquare.toX projection of the q-level lift two-cell

This file isolates the `qSquare.toX` verification equation that arises when
`Q.isPullback.twoCell_ext` is applied to a pair of 2-cells whose first member
is the q-level lift two-cell

  Q.isPullback.liftTwoCell W (coneQ source) (coneQ target) (qConeMorphism f).

The q-level projection field `Q.isPullback.liftTwoCell_toX` computes the
whiskering of that two-cell by `qSquare.toX`.  Since `qSquare.toX` is
`Q.toSource` and `(qConeMorphism f).toX` is `f.toX` definitionally, the
projection is exactly the displayed composite of the base-square cone
morphism `f`.

No sorry, no axiom, no extra assumption. -/

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
open LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal
open LeanFormal.IUT.XiFPaper.S2604M2BaseWitnessPartial
open LeanFormal.IUT.XiFPaper.S2608M2QConeMorphismActual
open LeanFormal.IUT.XiFPaper.S2610M2WitnessPartialActual
open LeanFormal.IUT.XiFPaper.S2611M2TwoCellExtActual

namespace LeanFormal.IUT.XiFPaper.S2615C3QTwoCellToXActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

/-- **`qSquare.toX` projection of the q-level lift two-cell.**

For base-square cones `source` and `target` and a base-square cone morphism
`f`, the q-level lift two-cell, transported to the two cones by `coneQ` and
`qConeMorphism`, whiskers with `qSquare.toX` to the explicit composite of
`f.toX` sandwiched between the q-level lift comparisons.  This is the
`qSquare.toX` equation consumed by `Q.isPullback.twoCell_ext`, with the two
sides displayed in terms of `f` rather than of `qConeMorphism f`. -/
theorem qSquare_liftTwoCell_toX
    (W : EtaleStackPseudofunctor S1726K)
    (source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W)
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target) :
    Pseudofunctor.StrongTrans.whiskerRight
      (Q.isPullback.liftTwoCell W
        (coneQ (m := m) (s := s) (vy := vy) (Q := Q) source)
        (coneQ (m := m) (s := s) (vy := vy) (Q := Q) target)
        (qConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f))
      (qSquare (m := m) (vy := vy) (Q := Q)).toX =
    (Q.isPullback.liftToX W
      (coneQ (m := m) (s := s) (vy := vy) (Q := Q) source)).hom
      ≫ f.toX
      ≫ (Q.isPullback.liftToX W
        (coneQ (m := m) (s := s) (vy := vy) (Q := Q) target)).inv :=
  Q.isPullback.liftTwoCell_toX W
    (coneQ (m := m) (s := s) (vy := vy) (Q := Q) source)
    (coneQ (m := m) (s := s) (vy := vy) (Q := Q) target)
    (qConeMorphism (m := m) (s := s) (vy := vy) (Q := Q) f)

#check qSquare_liftTwoCell_toX
#print axioms qSquare_liftTwoCell_toX

end LeanFormal.IUT.XiFPaper.S2615C3QTwoCellToXActual
end
