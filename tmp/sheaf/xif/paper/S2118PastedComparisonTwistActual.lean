/-
# S2118: the pasted-comparison twist for the concrete S2108 witness -- exact status

## The target (S2115PastedComparisonTwist, restricted to the concrete witness)

S2115 reduced the right-cancellation lemma to
`S2115PastedComparisonTwist`: for the pasting datum
`D = S2097Pasting f g T ptA Pg`, every weak witness `wP` of the pasted square
and every cone `s` over the lower square `D.square1`, the two canonical
comparison cells

* `alpha = S2107LiftToYIsoX D wP s`,  `beta = S2107LiftToYIsoY D wP s`

satisfy the cone-morphism equation over the upper square `D.square2`:

  `(alpha whisker D.x2) ; (S2107Sq2ConeOf D s).commutes = 
     (S2107ImageCone D.square2 (S2107ExtLift D wP s ; D.toY1)).commutes
       ; (beta whisker D.y2)`

S2115 left `wP` arbitrary.  The present file asks the question for the witness
that is actually used by the butterfly reduction, the transported witness
`wP = S2108PastedWitness f g T ptA Pg`, and records the exact answer.

## What is proved here (no sorry, no new axiom, no change of any definition)

1. `S2118ConcreteWitnessTwist`: the target equation with `wP` specialised to
   `S2108PastedWitness`.  This is the datum the butterfly reduction needs: the
   witness produced by S2108 is exactly the one fed to S2107/S2115.

2. `S2118ConcreteLift`, `S2118ConcreteLiftToX`, `S2118ConcreteLiftToY`: the
   S2108 transport is *definitionally transparent*.  The lift of the extended
   cone `S2107ExtCone D s` is `Pg.isPullback.lift` of the transported cone
   `S2118Conv`, and the two comparisons are (up to the leg 2-isomorphism
   `S2097LiftToB`) the two comparisons of `Pg.isPullback`.  Hence the target
   equation is, at the fibre level, an equation between the two *recorded*
   comparisons of the base-change presentation's own witness `Pg.isPullback`
   and the structure cell of the transported cone.  Nothing else is involved.

3. `S2118PresentationTwist`: **the exact first missing datum**, stated at the
   presentation square: the recorded comparisons of `Pg.isPullback` satisfy the
   twist for the transported cone `S2118Conv` (cone over the presentation
   square `mk Pg.toSource Pg.projectionMap.transformation g.map (ptA;f.map)
   Pg.commutes`).  It is a statement about `Pg` alone and does not mention the
   S2108 transport.

4. `S2118ConcreteWitnessTwist_of_general`: the general S2115 datum implies the
   concrete one, so everything proved in S2115 for the general twist (the
   S2099/S2096 fibre twist and the existence of the comparison
   `wP.lift (E s) ; D.toY1 ~ S2076Witness.lift (S2107Sq2ConeOf D s)`) applies
   verbatim to the concrete witness.

5. `S2118ConcreteWitnessTwist_implies_twist` and
   `S2118ConcreteWitnessTwist_implies_liftIso`: the concrete twist implies the
   fibre twist and the comparison isomorphism, by S2115's `S2115ImageConeTwistAt`
   and S2096's `S2096LiftUniq_of_projectionCompat`.  In particular the concrete
   twist is a *sufficient* input for the S2107 reduction.

## The exact first missing, and why the concrete witness does not close it

The cone-morphism equation is genuinely 2-categorical: a weak witness
`TwoPullbackWitness` records `lift`, `liftToX`, `liftToY` with no field
relating the two comparison 2-cells to the cone's commutes cell.  The S2108
transport does not change this: by §3 its comparisons *are* the presentation's
own comparisons, so the concrete equation is exactly a compatibility of
`Pg.isPullback` with the transported cone.

The fibre-level analysis (recorded here; not formalized) localises the content
precisely.  Write `l = Pg.isPullback.lift (S2118Conv s)`, let
`a = Pg.isPullback.liftToY (S2118Conv s)` and
`a' = Pg.isPullback.liftToX (S2118Conv s)`, and let `y = l.app U x`.  Expanding
the components at `(U, x)` gives

* `alpha_x = (c1^-1)_y ; ptA.map(a_y) ; (s.commutes)_x`, where
  `c1 = (S2086LiftToA).symm` and `a = liftToY` (S2118ConcreteLiftToX);
* `beta_x = (S2097LiftToB)_y ; a'_y`, where `a' = liftToX`
  (S2118ConcreteLiftToY);
* the target equation at `(U, x)` is equivalent to

  `(f.map) a'_y ; conv.commutes_y = (Pg.commutes)_y ; (ptA;f.map) a_y`

  i.e. exactly the presentation twist at `(U, y)`.

Two of the three inputs of that equivalence are automatic and available in the
tree: the components of `S2086LiftToA` and of `S2097LiftToB` are identities
(S2076's `gLiftToA`/`gLiftToB` are `eqToIso`s of functor equalities), and
the structure cell `((S2086Lift.app U).obj y).obj.hom` of the presentation
lift is the component of `S2086Cone.commutes`, hence `(Pg.commutes)_y ^-1`
(`gLiftApp_obj_hom`; equivalently S2115's computation of the image-cone
commutes cell), which is what makes the middle of the derivation cancel.  What
survives is precisely the compatibility of the *recorded* comparisons
`liftToX`/`liftToY` of `Pg.isPullback` with the commutes cell:
`S2118PresentationTwist`.

Precisely: `S2118PresentationTwist` (for all cones over the presentation
square) implies `S2118ConcreteWitnessTwist`; conversely the concrete twist
supplies the presentation twist only at the points `y = lift.app U x` lying in
the image of the lift, so the two statements are equivalent on the image of the
lift and the presentation form is the stronger, intrinsic one.  Neither
direction is formalized here (both are associativity bookkeeping at the level of
the fibre categories); the mathematical derivation above is the evidence.

The twist is not among the recorded fields: `isPullback` is an arbitrary
`TwoPullbackWitness`, whose definition (Iut/Foundations/Orbicurve.lean)
contains no equation linking `liftToX` and `liftToY`; the generic argument of
S2099/S2104/S2115 (the seven fields do not export the twist) indicates that it
does not follow from the API, and no proof of it exists in the tree.  The
geometric content that does supply it -- for the actual scheme-theoretic base
change the presentation square is a genuine 2-pullback, whose cone-category
equivalence makes the comparisons compatible with the structure cells -- is not
part of the recorded API.

Hence the honest answer to the task: the equation is **not** proved for
`wP = S2108PastedWitness`, and the exact first missing is
`S2118PresentationTwist`, the twist of the presentation's recorded witness at
the single transported cone.  It is stated, not assumed; the consequences of
the concrete twist are proved.

## Axiom footprint

Only `propext`, `Classical.choice` and `Quot.sound`; see the audit block.
No sorry, no new axiom, no fabricated witness.
-/

import tmp.sheaf.xif.paper.S2115UpperTwoCellFullActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2099BigSquareEssSurjActual
open LeanFormal.IUT.XiFPaper.S2101SiteNaturalityActual
open LeanFormal.IUT.XiFPaper.S2104ButterflyTwistActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2108PastedTransportActual
open LeanFormal.IUT.XiFPaper.S2115UpperTwoCellFullActual

universe u

/-! ## 1. The target: the twist for the concrete S2108 witness -/

/-- **The S2115 comparison twist for the concrete transported witness.**  For
`wP = S2108PastedWitness`, the two canonical comparison cells of S2107 form a
cone morphism from the image cone of `S2107ExtLift ; D.toY1` to
`S2107Sq2ConeOf D s`. -/
def S2118ConcreteWitnessTwist : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg).square1.Cone W),
    let D := S2097Pasting f g T ptA Pg
    let wP := S2108PastedWitness f g T ptA Pg
    Pseudofunctor.StrongTrans.whiskerRight (S2107LiftToYIsoX D wP s).hom D.x2 ≫
        (S2107Sq2ConeOf D s).commutes.hom =
      (S2107ImageCone D.square2
          (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1)).commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight (S2107LiftToYIsoY D wP s).hom D.y2

/-! ## 2. The presentation square and the transported cone -/

/-- The presentation square of `Pg`, in the exact structure form of the
recorded witness `Pg.isPullback`. -/
abbrev S2118PresentationSquare {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)) :
    EtalePseudofunctorSquare
      (schemeRepresentableEtalePseudofunctor S1726K Pg.pullbackScheme)
      B.source.fiber (schemeRepresentableEtalePseudofunctor S1726K T)
      C.source.fiber :=
  EtalePseudofunctorSquare.mk Pg.toSource Pg.projectionMap.transformation g.map
    (S2086PointC f ptA) Pg.commutes

/-- The cone over the presentation square obtained by transporting the extended
cone `S2107ExtCone D s` through the swap-and-leg-change of S2108.  Its
commutes cell is the inverse of the extended cone's commutes cell. -/
noncomputable def S2118Conv {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2097Pasting f g T ptA Pg).square1.Cone W) :
    (S2118PresentationSquare f g T ptA Pg).Cone W where
  toX := Pseudofunctor.StrongTrans.vcomp s.toY (S2097Pasting f g T ptA Pg).toY2
  toY := s.toX
  commutes := (S2107ExtCone (S2097Pasting f g T ptA Pg) s).commutes.symm

/-! ## 3. The transport is definitionally transparent -/

section Transport

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable (T : SchemeOverField S1726K)
variable (ptA : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
variable (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
variable {W : EtaleStackPseudofunctor S1726K}
variable (s : (S2097Pasting f g T ptA Pg).square1.Cone W)

/-- **The lift of the concrete witness is the presentation's lift.**  The S2108
transport of `S2107ExtCone D s` is the reversed transported cone, so the
S2108 witness lifts it by `Pg.isPullback.lift`. -/
theorem S2118ConcreteLift :
    (S2108PastedWitness f g T ptA Pg).lift W
        (S2107ExtCone (S2097Pasting f g T ptA Pg) s) =
      Pg.isPullback.lift W (S2118Conv f g T ptA Pg s) := rfl

/-- **The first comparison of the concrete witness is the presentation's
second comparison** (the S2097 base-pair swap exchanges them). -/
theorem S2118ConcreteLiftToX :
    (S2108PastedWitness f g T ptA Pg).liftToX W
        (S2107ExtCone (S2097Pasting f g T ptA Pg) s) =
      Pg.isPullback.liftToY W (S2118Conv f g T ptA Pg s) := rfl

/-- **The second comparison of the concrete witness is the presentation's first
comparison**, composed with the leg 2-isomorphism `S2097LiftToB` (the S2108
leg change). -/
theorem S2118ConcreteLiftToY :
    (S2108PastedWitness f g T ptA Pg).liftToY W
        (S2107ExtCone (S2097Pasting f g T ptA Pg) s) =
      (S2058WhiskerLeftIso
        ((S2108PastedWitness f g T ptA Pg).lift W
          (S2107ExtCone (S2097Pasting f g T ptA Pg) s))
        Pg.toSource
        (Pseudofunctor.StrongTrans.vcomp (S2086Lift f g T ptA Pg) (toB f g))
        (S2097LiftToB f g T ptA Pg).symm).symm.trans
      (Pg.isPullback.liftToX W (S2118Conv f g T ptA Pg s)) := rfl

end Transport

/-! ## 4. The exact first missing datum -/

/-- **The exact first missing datum.**  The two comparisons recorded by the
base-change presentation's own witness `Pg.isPullback` satisfy the twist for
the transported cone `S2118Conv`: they form a cone morphism from the image
cone of the presentation lift to the transported cone, over the presentation
square.

This is a statement about `Pg` alone.  It is not implied by the recorded
fields of `Pg.isPullback` (which contain no equation between `liftToX` and
`liftToY`); it is the geometric/full-universality content of the presentation
square.  It is stated here, not assumed. -/
def S2118PresentationTwist : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg).square1.Cone W),
    let c0 := S2118Conv f g T ptA Pg s
    Pseudofunctor.StrongTrans.whiskerRight (Pg.isPullback.liftToX W c0).hom g.map ≫
        c0.commutes.hom =
      (S2107ImageCone (S2118PresentationSquare f g T ptA Pg)
          (Pg.isPullback.lift W c0)).commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight (Pg.isPullback.liftToY W c0).hom
          (Pseudofunctor.StrongTrans.vcomp ptA f.map)

/-! ## 5. Relation to the general S2115 datum -/

/-- The general S2115 pasted-comparison twist implies the concrete one. -/
theorem S2118ConcreteWitnessTwist_of_general
    (h : S2115PastedComparisonTwist) : S2118ConcreteWitnessTwist := by
  intro A B C f g T ptA Pg W s
  exact h A B C f g T ptA Pg (S2108PastedWitness f g T ptA Pg) W s

/-- The concrete twist is the general twist at the concrete witness. -/
theorem S2118ConcreteWitnessTwist_iff_general_at_witness :
    S2118ConcreteWitnessTwist ↔
      (∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
        (T : SchemeOverField S1726K)
        (ptA : Pseudofunctor.StrongTrans
          (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
        (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
        (W : EtaleStackPseudofunctor S1726K)
        (s : (S2097Pasting f g T ptA Pg).square1.Cone W),
        let D := S2097Pasting f g T ptA Pg
        let wP := S2108PastedWitness f g T ptA Pg
        Pseudofunctor.StrongTrans.whiskerRight (S2107LiftToYIsoX D wP s).hom D.x2 ≫
            (S2107Sq2ConeOf D s).commutes.hom =
          (S2107ImageCone D.square2
              (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1)).commutes.hom ≫
            Pseudofunctor.StrongTrans.whiskerRight (S2107LiftToYIsoY D wP s).hom D.y2) :=
  Iff.rfl

/-! ## 6. Consequences of the concrete twist (the S2107 reduction inputs) -/

/-- **The concrete twist gives the fibre twist for the concrete witness.** -/
theorem S2118ConcreteWitnessTwist_implies_twist
    (h : S2118ConcreteWitnessTwist)
    (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg).square1.Cone W) :
    let D := S2097Pasting f g T ptA Pg
    let wP := S2108PastedWitness f g T ptA Pg
    S2099Twist f g (S2107Sq2ConeOf D s)
      (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1)
      (S2115PastedAlpha D wP s) (S2115PastedBeta D wP s) := by
  intro D wP
  have hcompat := h A B C f g T ptA Pg W s
  change Pseudofunctor.StrongTrans.whiskerRight (S2115PastedAlpha D wP s).hom D.x2 ≫
      (S2107Sq2ConeOf D s).commutes.hom =
    (S2107ImageCone D.square2
        (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1)).commutes.hom ≫
      Pseudofunctor.StrongTrans.whiskerRight (S2115PastedBeta D wP s).hom D.y2 at hcompat
  let m : (S2115UpperSquare f g).ConeMorphism
      (S2115UpperImageCone f g
        (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1))
      (S2107Sq2ConeOf D s) :=
    { toX := (S2115PastedAlpha D wP s).hom
      toY := (S2115PastedBeta D wP s).hom
      compatibility := hcompat }
  exact S2115ImageConeTwistAt f g (S2115PastedAlpha D wP s) (S2115PastedBeta D wP s)
    m rfl rfl

/-- **The concrete twist gives the comparison with the second leg.**  Under it,
`wP.lift (E s) ; D.toY1` is isomorphic to the S2076 lift of the upper cone
`S2107Sq2ConeOf D s`.  This is the comparison used by the right-cancellation
reduction (S2107's `S2107ExtLiftToY`). -/
theorem S2118ConcreteWitnessTwist_implies_liftIso
    (h : S2118ConcreteWitnessTwist)
    (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg).square1.Cone W) :
    let D := S2097Pasting f g T ptA Pg
    let wP := S2108PastedWitness f g T ptA Pg
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1)
      ((S2076Witness (f := f) (g := g)).lift W (S2107Sq2ConeOf D s))) := by
  intro D wP
  have hTw := S2118ConcreteWitnessTwist_implies_twist h A B C f g T ptA Pg W s
  have hcompat := S2115ProjectionCompat_of_twist f g
    (c := S2107Sq2ConeOf D s) (h := Pseudofunctor.StrongTrans.vcomp
      (S2107ExtLift D wP s) D.toY1) hTw
  exact ⟨S2096LiftUniq_of_projectionCompat (f := f) (g := g)
    (S2107Sq2ConeOf D s)
    (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1)
    (S2115PastedAlpha D wP s) (S2115PastedBeta D wP s) hcompat⟩

/-! ## 7. Checks and axiom audit -/

#check @S2118ConcreteWitnessTwist
#check @S2118PresentationSquare
#check @S2118Conv
#check @S2118ConcreteLift
#check @S2118ConcreteLiftToX
#check @S2118ConcreteLiftToY
#check @S2118PresentationTwist
#check @S2118ConcreteWitnessTwist_of_general
#check @S2118ConcreteWitnessTwist_iff_general_at_witness
#check @S2118ConcreteWitnessTwist_implies_twist
#check @S2118ConcreteWitnessTwist_implies_liftIso

#print axioms S2118ConcreteLift
#print axioms S2118ConcreteLiftToX
#print axioms S2118ConcreteLiftToY
#print axioms S2118ConcreteWitnessTwist_of_general
#print axioms S2118ConcreteWitnessTwist_implies_twist
#print axioms S2118ConcreteWitnessTwist_implies_liftIso

end LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual
