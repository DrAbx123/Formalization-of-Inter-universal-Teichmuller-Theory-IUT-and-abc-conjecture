import tmp.sheaf.xif.paper.S2121ChoiceFreeLowerWitnessActual

/-!
# S2124: the D.toY1 projection equation for the choice-free comparison

S2121 reduced the choice-free lower witness to the single equation family
S2121ToYEquation (the D.toY1 projection of the pasted two-cell
S2114PastedTwoCell).  This file proves it by the standard twoCell_ext
bookkeeping of the upper (iso-comma) witness S2076Witness:

* the D.xi leg: Coherence.S2114LowerLiftToACompat together with the pasted
  first projection equation S2114PastedTwoCell_toX give the explicit
  comparison composite of S2107LiftToYIsoX, and the choice-free comparison has
  exactly that composite as its D.xi-whiskering
  (S2121ChoiceFreeExtLiftToY_toX);
* the D.toY2 leg: the pasted second projection equation
  S2114PastedTwoCell_toY2, the comparison S2107LiftToYIsoY, and
  S2121ChoiceFreeExtLiftToY_toY;
* (S2076Witness f g).twoCell_ext finishes.

All normalisation uses rfl-unfoldings of the two comparison isomorphisms
(right-associated, matching the definitions) and Category.assoc only; no simp
set unfolding S2107LiftToYIsoX is used.

Consequences: S2121ToYEquation, plus the unconditional rebuilt lower witness
and butterfly assembly S2121RebuiltWitness / S2121ToAWitness, and their
S2118ConcreteWitnessTwist-conditional forms.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.tacticCheckInstances false

namespace LeanFormal.IUT.XiFPaper.S2124ToYEquationActual

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

universe u

section Main

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable (T : SchemeOverField S1726K)
variable (ptA : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
variable (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))

/-! ## 1. rfl-unfoldings of the two comparison isomorphisms -/

/-- Right-associated unfolding of the first upper comparison. -/
theorem S2124LiftToYIsoX_hom {W : EtaleStackPseudofunctor S1726K}
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
            (S2121D f g T ptA Pg).square1.toX)
          s.toX (S2121D f g T ptA Pg).x1
          (S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).hom ≫
        s.commutes.hom := rfl

/-- Unfolding of the inverse of the first upper comparison, in the
right-associated form used by Coherence.S2114LowerLiftToACompat. -/
theorem S2124LiftToYIsoX_inv {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).inv =
      s.commutes.inv ≫
        (S2058WhiskerRightIso
          (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
            (S2121D f g T ptA Pg).square1.toX)
          s.toX (S2121D f g T ptA Pg).x1
          (S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).inv ≫
        (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1).hom ≫
        (S2058WhiskerLeftIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toX1 (S2121D f g T ptA Pg).x1)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi)
          (S2121D f g T ptA Pg).c1).hom ≫
        (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).xi).inv := by
  have h : (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).inv =
      (((s.commutes.inv ≫
            (S2058WhiskerRightIso
              (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
                (S2121D f g T ptA Pg).square1.toX)
              s.toX (S2121D f g T ptA Pg).x1
              (S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).inv) ≫
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

/-- Right-associated unfolding of the second upper comparison. -/
theorem S2124LiftToYIsoY_hom {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    (S2107LiftToYIsoY (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom =
      (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
        (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).toY2).hom ≫
      (S2107ExtLiftToY2 (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom := rfl

/-- Right-associated unfolding of the inverse of the second upper comparison. -/
theorem S2124LiftToYIsoY_inv {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    (S2107LiftToYIsoY (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).inv =
      (S2107ExtLiftToY2 (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).inv ≫
      (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
        (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).toY2).inv := rfl

/-- The second pasted projection equation, stated with toY1. -/
theorem S2124PastedTwoCell_toY2 {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2121D f g T ptA Pg).square1.Cone W}
    (m : (S2121D f g T ptA Pg).square1.ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight (S2114PastedTwoCell f g T ptA Pg m)
        (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).toY2) =
      (S2107ExtLiftToY2 (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom ≫
        (Pseudofunctor.StrongTrans.whiskerRight m.toY (S2121D f g T ptA Pg).toY2) ≫
      (S2107ExtLiftToY2 (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t).inv :=
  S2114PastedTwoCell_toY2 f g T ptA Pg m


/-! ## 2. The two leg expansions of the pasted two-cell -/

/-- The D.xi leg, expanded into the explicit comparison composite of
S2107LiftToYIsoX, in fully right-associated form.  This is
Coherence.S2114LowerLiftToACompat at the actual butterfly datum, normalised by
Category.assoc. -/
theorem S2124PastedToXi {W : EtaleStackPseudofunctor S1726K}
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
                (S2121D f g T ptA Pg).square1.toX)
              s.toX (S2121D f g T ptA Pg).x1
              (S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).hom ≫
            s.commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight m.toY (S2121D f g T ptA Pg).xi ≫
        t.commutes.inv ≫
          (S2058WhiskerRightIso
            (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
              (S2121D f g T ptA Pg).square1.toX)
            t.toX (S2121D f g T ptA Pg).x1
            (S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)).inv ≫
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
                (S2121D f g T ptA Pg).square1.toX)
              s.toX (S2121D f g T ptA Pg).x1
              (S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)).hom ≫
            s.commutes.hom) ≫
        Pseudofunctor.StrongTrans.whiskerRight m.toY (S2121D f g T ptA Pg).xi ≫
        (t.commutes.inv ≫
          (S2058WhiskerRightIso
            (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
              (S2121D f g T ptA Pg).square1.toX)
            t.toX (S2121D f g T ptA Pg).x1
            (S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)).inv ≫
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
      (S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
      (S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
      s.commutes t.commutes
      (S2114PastedTwoCell_toX f g T ptA Pg m) m.compatibility
  rw [h]
  simp only [Category.assoc]

/-- The D.toY2 leg, expanded with the two associators. -/
theorem S2124PastedToY2 {W : EtaleStackPseudofunctor S1726K}
    (s t : (S2121D f g T ptA Pg).square1.Cone W)
    (m : (S2121D f g T ptA Pg).square1.ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight
        (Pseudofunctor.StrongTrans.whiskerRight (S2114PastedTwoCell f g T ptA Pg m)
          (S2121D f g T ptA Pg).toY1) (S2121D f g T ptA Pg).toY2
      = (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).toY2).hom ≫
        Pseudofunctor.StrongTrans.whiskerRight (S2114PastedTwoCell f g T ptA Pg m)
          (Pseudofunctor.StrongTrans.vcomp (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).toY2) ≫
        (S2058AssociatorIso (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) t)
          (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).toY2).inv :=
  Bicategory.whiskerRight_comp_symm (S2114PastedTwoCell f g T ptA Pg m)
    (S2121D f g T ptA Pg).toY1 (S2121D f g T ptA Pg).toY2

/-! ## 3. The two legs -/

/-- The D.xi leg of the equation, for the choice-free comparison. -/
theorem S2124XiLeg (h : S2121ComparisonTwist f g T ptA Pg) {W : EtaleStackPseudofunctor S1726K}
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
  rw [S2124PastedToXi f g T ptA Pg s t m]
  rw [S2124LiftToYIsoX_hom f g T ptA Pg s]
  rw [S2124LiftToYIsoX_inv f g T ptA Pg t]
  simp only [Category.assoc]

/-- The D.toY2 leg of the equation, for the choice-free comparison. -/
theorem S2124ToY2Leg (h : S2121ComparisonTwist f g T ptA Pg) {W : EtaleStackPseudofunctor S1726K}
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
  simp only [Category.assoc]

/-! ## 4. The equation and the unconditional consequences -/

/-- **The D.toY1 equation for the choice-free comparison.** -/
theorem S2124ToYEquation (h : S2121ComparisonTwist f g T ptA Pg) :
    S2121ToYEquation f g T ptA Pg h := by
  intro W s t m
  refine (S2076Witness (f := f) (g := g)).twoCell_ext W
    (Pseudofunctor.StrongTrans.whiskerRight (S2114PastedTwoCell f g T ptA Pg m)
      (S2121D f g T ptA Pg).square1.toY)
    ((S2121ChoiceFreeExtLiftToY f g T ptA Pg h s).hom ≫ m.toY ≫
      (S2121ChoiceFreeExtLiftToY f g T ptA Pg h t).inv) ?_ ?_
  · exact S2124XiLeg f g T ptA Pg h s t m
  · exact S2124ToY2Leg f g T ptA Pg h s t m

/-- The equation under the concrete-witness twist of S2118. -/
theorem S2124ToYEquation_of_concrete (h : S2118ConcreteWitnessTwist) :
    S2121ToYEquation f g T ptA Pg (S2121ComparisonTwist_of_concrete f g T ptA Pg h) :=
  S2124ToYEquation f g T ptA Pg _

/-- **The rebuilt lower witness, unconditionally.** -/
noncomputable def S2124RebuiltWitness (h : S2121ComparisonTwist f g T ptA Pg) :
    (S2121D f g T ptA Pg).square1.TwoPullbackWitness :=
  S2121RebuiltWitness f g T ptA Pg h (S2124ToYEquation f g T ptA Pg h)

/-- **The butterfly assembly, unconditionally.** -/
noncomputable def S2124ToAWitness (h : S2121ComparisonTwist f g T ptA Pg) :
    (S2086ToASquare f g T ptA Pg).TwoPullbackWitness :=
  S2121ToAWitness f g T ptA Pg h (S2124ToYEquation f g T ptA Pg h)

/-- The rebuilt lower witness under the concrete-witness twist of S2118. -/
noncomputable def S2124RebuiltWitness_of_concrete (h : S2118ConcreteWitnessTwist) :
    (S2121D f g T ptA Pg).square1.TwoPullbackWitness :=
  S2124RebuiltWitness f g T ptA Pg (S2121ComparisonTwist_of_concrete f g T ptA Pg h)

/-- The butterfly assembly under the concrete-witness twist of S2118. -/
noncomputable def S2124ToAWitness_of_concrete (h : S2118ConcreteWitnessTwist) :
    (S2086ToASquare f g T ptA Pg).TwoPullbackWitness :=
  S2124ToAWitness f g T ptA Pg (S2121ComparisonTwist_of_concrete f g T ptA Pg h)

end Main

/-! ## 5. Checks and axiom audit -/

#check @S2124LiftToYIsoX_hom
#check @S2124LiftToYIsoX_inv
#check @S2124LiftToYIsoY_hom
#check @S2124LiftToYIsoY_inv
#check @S2124PastedToXi
#check @S2124PastedToY2
#check @S2124XiLeg
#check @S2124ToY2Leg
#check @S2124ToYEquation
#check @S2124ToYEquation_of_concrete
#check @S2124RebuiltWitness
#check @S2124ToAWitness

#print axioms S2124LiftToYIsoX_hom
#print axioms S2124LiftToYIsoX_inv
#print axioms S2124LiftToYIsoY_hom
#print axioms S2124LiftToYIsoY_inv
#print axioms S2124PastedTwoCell_toY2
#print axioms S2124PastedToXi
#print axioms S2124PastedToY2
#print axioms S2124XiLeg
#print axioms S2124ToY2Leg
#print axioms S2124ToYEquation
#print axioms S2124RebuiltWitness
#print axioms S2124ToAWitness

end LeanFormal.IUT.XiFPaper.S2124ToYEquationActual