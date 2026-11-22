import tmp.sheaf.xif.paper.S2124ToYEquationActual

/-!
# S2127: the two legs of the choice-free D.toY1 equation, unconditionally

S2124 reduced the choice-free lower witness to the two leg equations
`S2124XiLegStatement` and `S2124ToY2LegStatement` (their conjunction is
`S2124Legs`), and proved the D.toY1 equation from them by the upper
iso-comma `twoCell_ext`.  This file proves the two legs themselves.

The technical point is a definiteness issue: `S2107ExtLiftToX` is stated with
`D.square1.toX` (the projection of the lower square), while
`S2107LiftToYIsoX` is stated with `D.toX1`.  The two are definitionally
equal (the latter is the field of the former), but the defeq is only visible
above reducible transparency, which is not enough for the final associativity
normalisation.  We therefore repackage the comparison once:

* `S2124ExtLiftToX` has the type with `D.toX1` (its body is
  `S2107ExtLiftToX`);
* `S2127LiftToYIsoX_hom` / `S2127LiftToYIsoX_inv` are the rfl-unfoldings of
  the comparison stated with `D.toX1` and `S2124ExtLiftToX`;
* `S2127PastedToXi` is S2114's `S2114LowerLiftToACompat` at the actual
  butterfly datum with the same repackaging.

Then each leg is a two-step rewrite with the prescribed projections followed
by `simp only [Category.assoc]`.  No new mathematical input is used.

Consequences (unconditional): `S2124Legs`, `S2121ToYEquation`,
`S2121RebuiltWitness`, `S2121ToAWitness`.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.tacticCheckInstances false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2127ToYLegsActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2099BigSquareEssSurjActual
open LeanFormal.IUT.XiFPaper.S2101SiteNaturalityActual
open LeanFormal.IUT.XiFPaper.S2104ButterflyTwistActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2108PastedTransportActual
open LeanFormal.IUT.XiFPaper.S2114CanonicalLiftTwoCellActual
open LeanFormal.IUT.XiFPaper.S2115UpperTwoCellFullActual
open LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual
open LeanFormal.IUT.XiFPaper.S2121ChoiceFreeLowerWitnessActual
open LeanFormal.IUT.XiFPaper.S2124ToYEquationActual

universe u

section Main

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable (T : SchemeOverField S1726K)
variable (ptA : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
variable (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))

/-! ## 0. Repackaging the first-leg comparison with `D.toX1` -/

/-- The canonical lift's comparison with the first leg, stated with
`D.toX1` (the form used by `S2107LiftToYIsoX`). -/
noncomputable def S2124ExtLiftToX (D : S2058Pasting (F := S1726K))
    (wP : D.squareP.TwoPullbackWitness) {W : EtaleStackPseudofunctor S1726K}
    (s : D.square1.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toX1) s.toX :=
  S2107ExtLiftToX D wP s

/-- The cone's commutation iso, restated with the fields `D.x1`, `D.xi` of the
pasting datum (rather than the projections of `D.square1`).  This keeps every
composite in the leg proofs syntactically matched at `instances` transparency. -/
noncomputable def S2127Commutes (D : S2058Pasting (F := S1726K))
    {W : EtaleStackPseudofunctor S1726K} (s : D.square1.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp s.toX D.x1)
      (Pseudofunctor.StrongTrans.vcomp s.toY D.xi) :=
  s.commutes

/-! ## 1. rfl-unfoldings with the repackaged comparison -/

/-- Right-associated unfolding of the first upper comparison. -/
theorem S2127LiftToYIsoX_hom {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom =
      (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi).hom ≫
        (S2058WhiskerLeftIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi)
          (S2121D f g T ptA Pg).c1).symm.hom ≫
        (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1).symm.hom ≫
        (S2058WhiskerRightIso
          (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
            (S2121D f g T ptA Pg).toX1)
          s.toX (S2121D f g T ptA Pg).x1
          (S2124ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).hom ≫
        (S2127Commutes (S2121D f g T ptA Pg) s).hom := rfl

/-- Unfolding of the inverse of the first upper comparison, in the
right-associated form used by Coherence.S2114LowerLiftToACompat. -/
theorem S2127LiftToYIsoX_inv {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).inv =
      (S2127Commutes (S2121D f g T ptA Pg) s).inv ≫
        (S2058WhiskerRightIso
          (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
            (S2121D f g T ptA Pg).toX1)
          s.toX (S2121D f g T ptA Pg).x1
          (S2124ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).inv ≫
        (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1).hom ≫
        (S2058WhiskerLeftIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi)
          (S2121D f g T ptA Pg).c1).hom ≫
        (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi).inv := by
  have h : (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).inv =
      ((((S2127Commutes (S2121D f g T ptA Pg) s).inv ≫
            (S2058WhiskerRightIso
              (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
                (S2121D f g T ptA Pg).toX1)
              s.toX (S2121D f g T ptA Pg).x1
              (S2124ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).inv) ≫
          (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
            (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1).hom) ≫
        (S2058WhiskerLeftIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi)
          (S2121D f g T ptA Pg).c1).hom) ≫
      (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
        (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi).inv := rfl
  rw [h]
  simp only [Category.assoc]
/-! ## 2. The two leg expansions of the pasted two-cell -/

/-- The D.xi leg, expanded into the explicit comparison composite of
S2107LiftToYIsoX, in fully right-associated form.  This is
Coherence.S2114LowerLiftToACompat at the actual butterfly datum, normalised by
Category.assoc. -/
theorem S2127PastedToXi {W : EtaleStackPseudofunctor S1726K}
    (s t : (S2121D f g T ptA Pg).square1.Cone W)
    (m : (S2121D f g T ptA Pg).square1.ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight
        (Pseudofunctor.StrongTrans.whiskerRight (S2114PastedTwoCell f g T ptA Pg m)
          (S2121D f g T ptA Pg).toY1) (S2121D f g T ptA Pg).xi
      = (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
              (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi).hom ≫
            (S2058WhiskerLeftIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
              (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1)
              (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi)
              (S2121D f g T ptA Pg).c1).symm.hom ≫
            (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
              (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1).symm.hom ≫
            (S2058WhiskerRightIso
              (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
                (S2121D f g T ptA Pg).toX1)
              s.toX (S2121D f g T ptA Pg).x1
              (S2124ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).hom ≫
            (S2127Commutes (S2121D f g T ptA Pg) s).hom ≫
        Pseudofunctor.StrongTrans.whiskerRight m.toY (S2121D f g T ptA Pg).xi ≫
        (S2127Commutes (S2121D f g T ptA Pg) t).inv ≫
          (S2058WhiskerRightIso
            (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
              (S2121D f g T ptA Pg).toX1)
            t.toX (S2121D f g T ptA Pg).x1
            (S2124ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)).inv ≫
          (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
            (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1).hom ≫
          (S2058WhiskerLeftIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
            (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1)
            (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi)
            (S2121D f g T ptA Pg).c1).hom ≫
          (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
            (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi).inv := by
  have h : Pseudofunctor.StrongTrans.whiskerRight
        (Pseudofunctor.StrongTrans.whiskerRight (S2114PastedTwoCell f g T ptA Pg m)
          (S2121D f g T ptA Pg).toY1) (S2121D f g T ptA Pg).xi
      = ((S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
              (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi).hom ≫
            (S2058WhiskerLeftIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
              (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1)
              (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi)
              (S2121D f g T ptA Pg).c1).symm.hom ≫
            (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
              (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1).symm.hom ≫
            (S2058WhiskerRightIso
              (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
                (S2121D f g T ptA Pg).toX1)
              s.toX (S2121D f g T ptA Pg).x1
              (S2124ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).hom ≫
            (S2127Commutes (S2121D f g T ptA Pg) s).hom) ≫
        Pseudofunctor.StrongTrans.whiskerRight m.toY (S2121D f g T ptA Pg).xi ≫
        ((S2127Commutes (S2121D f g T ptA Pg) t).inv ≫
          (S2058WhiskerRightIso
            (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
              (S2121D f g T ptA Pg).toX1)
            t.toX (S2121D f g T ptA Pg).x1
            (S2124ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)).inv ≫
          (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
            (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1).hom ≫
          (S2058WhiskerLeftIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
            (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1)
            (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi)
            (S2121D f g T ptA Pg).c1).hom ≫
          (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
            (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi).inv) :=
    Coherence.S2114LowerLiftToACompat (Bc := EtaleStackPseudofunctor S1726K)
      (a := W) (P := (S2121D f g T ptA Pg).P) (X := (S2121D f g T ptA Pg).X)
      (Y := (S2121D f g T ptA Pg).Ys) (Z := (S2121D f g T ptA Pg).Zs)
      (l_s := S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
      (l_t := S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
      (S2114PastedTwoCell f g T ptA Pg m)
      (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).toY1
      (S2121D f g T ptA Pg).x1 (S2121D f g T ptA Pg).xi (S2121D f g T ptA Pg).c1
      m.toX m.toY
      (S2124ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
      (S2124ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
      (S2127Commutes (S2121D f g T ptA Pg) s)
      (S2127Commutes (S2121D f g T ptA Pg) t)
      (S2114PastedTwoCell_toX f g T ptA Pg m) m.compatibility
  rw [h]
  simp only [Category.assoc]
/-! ## 2. The two legs -/

/-- The D.xi leg of the equation, for the choice-free comparison. -/
theorem S2127XiLeg (h : S2121ComparisonTwist f g T ptA Pg) {W : EtaleStackPseudofunctor S1726K}
    (s t : (S2121D f g T ptA Pg).square1.Cone W)
    (m : (S2121D f g T ptA Pg).square1.ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight
        (Pseudofunctor.StrongTrans.whiskerRight (S2114PastedTwoCell f g T ptA Pg m)
          (S2121D f g T ptA Pg).toY1) (S2121D f g T ptA Pg).xi
      = Pseudofunctor.StrongTrans.whiskerRight
          ((S2121ChoiceFreeExtLiftToY f g T ptA Pg h s).hom ≫ m.toY ≫
            (S2121ChoiceFreeExtLiftToY f g T ptA Pg h t).inv) (S2121D f g T ptA Pg).xi := by
  rw [S2121STWhiskerRight_comp]
  rw [S2121STWhiskerRight_comp]
  rw [S2121ChoiceFreeExtLiftToY_toX f g T ptA Pg h s]
  rw [S2121STWhiskerRight_inv_of_hom_eq
    (f := Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
      (S2121D f g T ptA Pg).square1.toY)
    (g := t.toY) (k := (S2121D f g T ptA Pg).xi)
    (e := S2121ChoiceFreeExtLiftToY f g T ptA Pg h t)
    (θ := S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
    (S2121ChoiceFreeExtLiftToY_toX f g T ptA Pg h t)]
  rw [S2127PastedToXi f g T ptA Pg s t m]
  rw [S2127LiftToYIsoX_hom f g T ptA Pg s]
  rw [S2127LiftToYIsoX_inv f g T ptA Pg t]
  simp only [Category.assoc]

/-- The D.toY2 leg of the equation, for the choice-free comparison. -/
theorem S2127ToY2Leg (h : S2121ComparisonTwist f g T ptA Pg) {W : EtaleStackPseudofunctor S1726K}
    (s t : (S2121D f g T ptA Pg).square1.Cone W)
    (m : (S2121D f g T ptA Pg).square1.ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight
        (Pseudofunctor.StrongTrans.whiskerRight (S2114PastedTwoCell f g T ptA Pg m)
          (S2121D f g T ptA Pg).toY1) (S2121D f g T ptA Pg).toY2
      = Pseudofunctor.StrongTrans.whiskerRight
          ((S2121ChoiceFreeExtLiftToY f g T ptA Pg h s).hom ≫ m.toY ≫
            (S2121ChoiceFreeExtLiftToY f g T ptA Pg h t).inv) (S2121D f g T ptA Pg).toY2 := by
  rw [S2121STWhiskerRight_comp]
  rw [S2121STWhiskerRight_comp]
  rw [S2121ChoiceFreeExtLiftToY_toY f g T ptA Pg h s]
  rw [S2121STWhiskerRight_inv_of_hom_eq
    (f := Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
      (S2121D f g T ptA Pg).square1.toY)
    (g := t.toY) (k := (S2121D f g T ptA Pg).toY2)
    (e := S2121ChoiceFreeExtLiftToY f g T ptA Pg h t)
    (θ := S2107LiftToYIsoY (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
    (S2121ChoiceFreeExtLiftToY_toY f g T ptA Pg h t)]
  rw [S2124PastedToY2 f g T ptA Pg s t m]
  rw [S2124PastedTwoCell_toY2 f g T ptA Pg m]
  rw [S2124LiftToYIsoY_hom f g T ptA Pg s]
  rw [S2124LiftToYIsoY_inv f g T ptA Pg t]
  repeat rw [Category.assoc]

/-! ## 3. The two leg statements, the equation, and the unconditional witnesses -/

/-- `S2124XiLegStatement`, proved. -/
theorem S2127XiLegStatement (h : S2121ComparisonTwist f g T ptA Pg) :
    S2124XiLegStatement f g T ptA Pg h := by
  intro W s t m
  change Pseudofunctor.StrongTrans.whiskerRight
      (Pseudofunctor.StrongTrans.whiskerRight (S2114PastedTwoCell f g T ptA Pg m)
        (S2121D f g T ptA Pg).toY1) (S2121D f g T ptA Pg).xi =
    Pseudofunctor.StrongTrans.whiskerRight
      ((S2121ChoiceFreeExtLiftToY f g T ptA Pg h s).hom ≫ m.toY ≫
        (S2121ChoiceFreeExtLiftToY f g T ptA Pg h t).inv) (S2121D f g T ptA Pg).xi
  exact S2127XiLeg f g T ptA Pg h s t m

/-- `S2124ToY2LegStatement`, proved. -/
theorem S2127ToY2LegStatement (h : S2121ComparisonTwist f g T ptA Pg) :
    S2124ToY2LegStatement f g T ptA Pg h := by
  intro W s t m
  change Pseudofunctor.StrongTrans.whiskerRight
      (Pseudofunctor.StrongTrans.whiskerRight (S2114PastedTwoCell f g T ptA Pg m)
        (S2121D f g T ptA Pg).toY1) (S2121D f g T ptA Pg).toY2 =
    Pseudofunctor.StrongTrans.whiskerRight
      ((S2121ChoiceFreeExtLiftToY f g T ptA Pg h s).hom ≫ m.toY ≫
        (S2121ChoiceFreeExtLiftToY f g T ptA Pg h t).inv) (S2121D f g T ptA Pg).toY2
  exact S2127ToY2Leg f g T ptA Pg h s t m

/-- `S2124Legs`, unconditionally. -/
theorem S2127Legs (h : S2121ComparisonTwist f g T ptA Pg) :
    S2124Legs f g T ptA Pg h :=
  ⟨S2127XiLegStatement f g T ptA Pg h, S2127ToY2LegStatement f g T ptA Pg h⟩

/-- The choice-free D.toY1 equation, unconditionally. -/
theorem S2127ToYEquation (h : S2121ComparisonTwist f g T ptA Pg) :
    S2121ToYEquation f g T ptA Pg h :=
  S2124ToYEquation_of_legs f g T ptA Pg h (S2127Legs f g T ptA Pg h)

/-- The rebuilt lower witness, unconditionally. -/
noncomputable def S2127RebuiltWitness (h : S2121ComparisonTwist f g T ptA Pg) :
    (S2121D f g T ptA Pg).square1.TwoPullbackWitness :=
  S2121RebuiltWitness f g T ptA Pg h (S2127ToYEquation f g T ptA Pg h)

/-- The butterfly assembly, unconditionally. -/
noncomputable def S2127ToAWitness (h : S2121ComparisonTwist f g T ptA Pg) :
    (S2086ToASquare f g T ptA Pg).TwoPullbackWitness :=
  S2121ToAWitness f g T ptA Pg h (S2127ToYEquation f g T ptA Pg h)

end Main

/-! ## 4. Checks and axiom audit -/

#check @S2124ExtLiftToX
#check @S2127LiftToYIsoX_hom
#check @S2127LiftToYIsoX_inv
#check @S2127PastedToXi
#check @S2127XiLeg
#check @S2127ToY2Leg
#check @S2127XiLegStatement
#check @S2127ToY2LegStatement
#check @S2127Legs
#check @S2127ToYEquation
#check @S2127RebuiltWitness
#check @S2127ToAWitness

#print axioms S2124ExtLiftToX
#print axioms S2127LiftToYIsoX_hom
#print axioms S2127LiftToYIsoX_inv
#print axioms S2127PastedToXi
#print axioms S2127XiLeg
#print axioms S2127ToY2Leg
#print axioms S2127XiLegStatement
#print axioms S2127ToY2LegStatement
#print axioms S2127Legs
#print axioms S2127ToYEquation
#print axioms S2127RebuiltWitness
#print axioms S2127ToAWitness

end LeanFormal.IUT.XiFPaper.S2127ToYLegsActual