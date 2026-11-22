import tmp.sheaf.xif.paper.S2114CanonicalLiftTwoCellActual
import tmp.sheaf.xif.paper.S2115UpperTwoCellFullActual
import tmp.sheaf.xif.paper.S2118PastedComparisonTwistActual
/-!
# S2121: the choice-free lower witness for the butterfly pasting -- exact status

## The task

S2114 reduced `S2107CanonicalLiftTwoCell` to the single equation family
`S2114ToYEquation` (the `D.toY1` projection equation of the pasted two-cell
`S2114PastedTwoCell`), and to the upper-comparison form
`S2114ChosenComparisonCompat`.  The comparison `S2107ExtLiftToY` used there is
built by `Classical.choice` applied to the *bare* essential surjectivity `h2`
of the upper iso-comma square; nothing constrains the chosen comparison, so
the `D.toY1` equation is not derivable from the recorded fields (S2114, S2115,
S2118).

This file carries out the choice-free reconstruction: replace the choice by
the *explicit* S2101/S2096 comparison, whose projections are prescribed by the
pasted comparison cells.  The construction uses no `Classical.choice`: the only
input is a *proof* (the upper twist) and the comparison is a definition.

## What is proved here (no sorry, no new axiom, EXIT 0)

1. `S2121LiftUniq_of_projectionCompat_toA` / `_toB`: the S2101 site-level
   comparison `S2096LiftUniq_of_projectionCompat` has exactly the prescribed
   two projections.  (S2115 only derived this inside an existential; here it
   is a standalone lemma.)

2. `S2121ComparisonTwist`: the twist input at the concrete S2108 pasted
   witness, definitionally the restriction of S2118's
   `S2118ConcreteWitnessTwist` to the fixed butterfly datum;
   `S2121ComparisonTwist_of_concrete` derives it from S2118's closed form, and
   `S2121ComparisonTwist_implies_twist` converts it into the fibre twist
   `S2099Twist` of the pasted comparison pair (S2101's compatibility input).

3. `S2121ReflTwist`: the twist of the identity comparison is automatic, since
   `S2107Sq2ConeOf D s` is definitionally the image cone of `s.toY`.

4. `S2121UpperComparison`, `S2121CanonicalComparison` and
   `S2121ChoiceFreeExtLiftToY`: the choice-free replacement for
   `S2107ExtLiftToY`.  No `Classical.choice` occurs in these definitions.

5. `S2121ChoiceFreeExtLiftToY_toX` / `_toY` and `S2121ChoiceFreeCompat_holds`:
   **the choice-free comparison has exactly the two pasted comparison cells as
   its upper-square projections.**  This is the choice-free form of
   S2114ChosenComparisonCompat: the compatibility is a theorem, not a choice.

6. `S2121ToYEquation`, `S2121RebuiltWitness`, `S2121ToAWitness`: the
   `D.toY1` equation for the rebuilt comparison is isolated as a
   named statement, and the rebuilt lower witness together with the actual
   base-change assembly follow from it.  The witness has `liftToX` equal to
   S2107's canonical comparison and `liftToY` equal to the choice-free
   comparison; every field is discharged except the `D.toY1` equation.

## The exact first missing

1. **The upper twist** `S2118ConcreteWitnessTwist` (equivalently, at the
   presentation, `S2118PresentationTwist`; S2115's general
   `S2115PastedComparisonTwist` is stronger).  It is the only external input
   of the choice-free comparison: without it the pasted comparison pair has no
   prescribed `S2096ProjectionCompatibility`, and S2118 records that the seven
   recorded fields of a `TwoPullbackWitness` do not imply it.
2. **The `D.toY1` equation itself** (`S2121ToYEquation`).  Given the two
   projection equations of the choice-free comparison, it is the standard
   `twoCell_ext` bookkeeping of the upper witness: whisker the claimed equality
   by the upper square's two legs, use the pasted first projection equation
   plus `S2114LowerLiftToACompat` (S2114, proved) on the `D.xi` leg, use the
   pasted second projection equation plus `S2107LiftToYIsoY` on the `D.toY2`
   leg, and apply `(S2076Witness f g).twoCell_ext`.  This derivation is
   mathematically complete but its associativity normalisation is *not*
   formalised in this file: it is recorded as the named statement
   `S2121ToYEquation` (a `def`, not an axiom and not a `sorry`; the conditional
   consequences are proved).

Accordingly, the literal `S2114ToYEquation` and `S2114ChosenComparisonCompat`
are **not** proved: they concern the `Classical.choice` comparison, whose
projections are unknown.  What is proved is that the *choice-free* comparison
has those projections and that the whole lower-witness/assembly interface is
reduced to the single equation `S2121ToYEquation`.

## Axiom footprint

Only `propext`, `Classical.choice` and `Quot.sound`; see the audit block at the
end.  `Classical.choice` is *not* applied to the bare essential surjectivity `h2`
here: the comparison is the explicit S2101/S2096 assembly, and its projections
are theorems.  The axiom is still reported because the imported S2101/S2076/S2108
constructions and the ambient category theory use it, as everywhere in this
tree; this file adds no new use of it for selecting a comparison.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2121ChoiceFreeLowerWitnessActual

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

universe u

/-! ## 1. The choice-free projection lemmas for the S2101 comparison -/

section Projection

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- First projection of the S2101/S2096 comparison. -/
theorem S2121LiftUniq_of_projectionCompat_toA
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2076Square (f := f) (g := g)).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY)
    (hcompat : S2096ProjectionCompatibility (f := f) (g := g)
      (S2076ConeToGeneral (f := f) (g := g) c) h eX eY) :
    Pseudofunctor.StrongTrans.whiskerRight
        (S2096LiftUniq_of_projectionCompat (f := f) (g := g) c h eX eY hcompat).hom
        (toA f g) =
      eX.hom ≫ ((S2076Witness (f := f) (g := g)).liftToX W c).inv := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext U
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  have hfst := S2096FibreIso_hom_fst_app (f := f) (g := g)
    (S2076ConeToGeneral (f := f) (g := g) c) h eX eY U (hcompat U) x
  have hL : ((Pseudofunctor.StrongTrans.whiskerRight
        (S2096LiftUniq_of_projectionCompat (f := f) (g := g) c h eX eY hcompat).hom
        (toA f g)).as.app U).toNatTrans.app x =
      (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map
        ((S2096FibreIso (f := f) (g := g)
          (S2076ConeToGeneral (f := f) (g := g) c) h eX eY U (hcompat U)).hom.app x) := rfl
  rw [hL, hfst]
  rw [show (eX.hom ≫ ((S2076Witness (f := f) (g := g)).liftToX W c).inv) =
      (eX.hom ≫ (gLiftToA (f := f) (g := g)
        (S2076ConeToGeneral (f := f) (g := g) c)).inv) from rfl]
  rw [show (((eX.hom ≫ (gLiftToA (f := f) (g := g)
        (S2076ConeToGeneral (f := f) (g := g) c)).inv).as.app U).toNatTrans.app x) =
      (eX.hom.as.app U).toNatTrans.app x by
    rw [show (eX.hom ≫ (gLiftToA (f := f) (g := g)
        (S2076ConeToGeneral (f := f) (g := g) c)).inv).as.app U =
        (eX.hom.as.app U ≫ (gLiftToA (f := f) (g := g)
          (S2076ConeToGeneral (f := f) (g := g) c)).inv.as.app U) from rfl]
    rw [Cat.Hom₂.comp_app, gLiftToA_inv_app_as]
    erw [Category.comp_id]]
  rfl

/-- Second projection of the S2101/S2096 comparison. -/
theorem S2121LiftUniq_of_projectionCompat_toB
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2076Square (f := f) (g := g)).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY)
    (hcompat : S2096ProjectionCompatibility (f := f) (g := g)
      (S2076ConeToGeneral (f := f) (g := g) c) h eX eY) :
    Pseudofunctor.StrongTrans.whiskerRight
        (S2096LiftUniq_of_projectionCompat (f := f) (g := g) c h eX eY hcompat).hom
        (toB f g) =
      eY.hom ≫ ((S2076Witness (f := f) (g := g)).liftToY W c).inv := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext U
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  have hsnd := S2096FibreIso_hom_snd_app (f := f) (g := g)
    (S2076ConeToGeneral (f := f) (g := g) c) h eX eY U (hcompat U) x
  have hL : ((Pseudofunctor.StrongTrans.whiskerRight
        (S2096LiftUniq_of_projectionCompat (f := f) (g := g) c h eX eY hcompat).hom
        (toB f g)).as.app U).toNatTrans.app x =
      (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map
        ((S2096FibreIso (f := f) (g := g)
          (S2076ConeToGeneral (f := f) (g := g) c) h eX eY U (hcompat U)).hom.app x) := rfl
  rw [hL, hsnd]
  rw [show (eY.hom ≫ ((S2076Witness (f := f) (g := g)).liftToY W c).inv) =
      (eY.hom ≫ (gLiftToB (f := f) (g := g)
        (S2076ConeToGeneral (f := f) (g := g) c)).inv) from rfl]
  rw [show (((eY.hom ≫ (gLiftToB (f := f) (g := g)
        (S2076ConeToGeneral (f := f) (g := g) c)).inv).as.app U).toNatTrans.app x) =
      (eY.hom.as.app U).toNatTrans.app x by
    rw [show (eY.hom ≫ (gLiftToB (f := f) (g := g)
        (S2076ConeToGeneral (f := f) (g := g) c)).inv).as.app U =
        (eY.hom.as.app U ≫ (gLiftToB (f := f) (g := g)
          (S2076ConeToGeneral (f := f) (g := g) c)).inv.as.app U) from rfl]
    rw [Cat.Hom₂.comp_app, gLiftToB_inv_app_as]
    erw [Category.comp_id]]
  rfl

end Projection

/-! ## 2. The concrete data and the twist input -/

section Actual

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable (T : SchemeOverField S1726K)
variable (ptA : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
variable (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))

/-- The actual S2097 pasting datum. -/
abbrev S2121D : S2058Pasting (F := S1726K) := S2097Pasting f g T ptA Pg

/-- The concrete S2108 pasted witness. -/
abbrev S2121WP : (S2121D f g T ptA Pg).squareP.TwoPullbackWitness :=
  S2108PastedWitness f g T ptA Pg

/-- The S2076 upper witness. -/
abbrev S2121W2 : (S2121D f g T ptA Pg).square2.TwoPullbackWitness :=
  S2076Witness (f := f) (g := g)

/-- The twist input at the concrete pasted witness: the compatibility of the
two pasted comparison cells with the upper square's commutes cell.  This is
S2118's concrete-witness twist specialised to the fixed butterfly datum. -/
def S2121ComparisonTwist : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K)
    (s : (S2121D f g T ptA Pg).square1.Cone W),
    Pseudofunctor.StrongTrans.whiskerRight
        (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom
        (S2121D f g T ptA Pg).x2 ≫
      (S2107Sq2ConeOf (S2121D f g T ptA Pg) s).commutes.hom =
    (S2107ImageCone (S2121D f g T ptA Pg).square2
        (Pseudofunctor.StrongTrans.vcomp
          (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
          (S2121D f g T ptA Pg).toY1)).commutes.hom ≫
      Pseudofunctor.StrongTrans.whiskerRight
        (S2107LiftToYIsoY (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom
        (S2121D f g T ptA Pg).y2

/-- The general S2118 concrete-witness twist gives the local twist. -/
theorem S2121ComparisonTwist_of_concrete
    (h : S2118ConcreteWitnessTwist) : S2121ComparisonTwist f g T ptA Pg :=
  fun W s => h A B C f g T ptA Pg W s

/-- The local twist is the S2099 twist of the pasted comparison pair. -/
theorem S2121ComparisonTwist_implies_twist
    (h : S2121ComparisonTwist f g T ptA Pg)
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    let D := S2121D f g T ptA Pg
    let wP := S2121WP f g T ptA Pg
    S2099Twist f g (S2107Sq2ConeOf D s)
      (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1)
      (S2115PastedAlpha D wP s) (S2115PastedBeta D wP s) := by
  intro D wP
  have hcompat := h W s
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

/-- The twist of the identity comparison is automatic: the upper cone
S2107Sq2ConeOf D s is definitionally the image cone of s.toY. -/
theorem S2121ReflTwist
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    let D := S2121D f g T ptA Pg
    S2099Twist f g (S2107Sq2ConeOf D s) s.toY
      (Iso.refl (Pseudofunctor.StrongTrans.vcomp s.toY (toA f g)))
      (Iso.refl (Pseudofunctor.StrongTrans.vcomp s.toY (toB f g))) := by
  intro D U x
  exact S2115ImageConeTwistAt f g
    (Iso.refl (Pseudofunctor.StrongTrans.vcomp s.toY (toA f g)))
    (Iso.refl (Pseudofunctor.StrongTrans.vcomp s.toY (toB f g)))
    (S2115ConeId f g (S2107Sq2ConeOf D s)) rfl rfl U x

/-- The choice-free pasted comparison, built from the twist by S2101's
site-level assembly. -/
noncomputable def S2121UpperComparison
    (h : S2121ComparisonTwist f g T ptA Pg)
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
        (S2121D f g T ptA Pg).toY1)
      ((S2076Witness (f := f) (g := g)).lift W
        (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)) :=
  S2096LiftUniq_of_projectionCompat (f := f) (g := g)
    (c := S2107Sq2ConeOf (S2121D f g T ptA Pg) s)
    (h := Pseudofunctor.StrongTrans.vcomp
      (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
      (S2121D f g T ptA Pg).toY1)
    (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
    (S2107LiftToYIsoY (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
    (S2115ProjectionCompat_of_twist f g
      (S2121ComparisonTwist_implies_twist f g T ptA Pg h s))

/-- The canonical comparison of the cone itself with the upper lift. -/
noncomputable def S2121CanonicalComparison
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    Iso s.toY
      ((S2076Witness (f := f) (g := g)).lift W
        (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)) :=
  S2096LiftUniq_of_projectionCompat (f := f) (g := g)
    (c := S2107Sq2ConeOf (S2121D f g T ptA Pg) s)
    (h := s.toY)
    (Iso.refl (Pseudofunctor.StrongTrans.vcomp s.toY (toA f g)))
    (Iso.refl (Pseudofunctor.StrongTrans.vcomp s.toY (toB f g)))
    (S2115ProjectionCompat_of_twist f g
      (S2121ReflTwist f g T ptA Pg s))

/-- The choice-free replacement for S2107ExtLiftToY.  No Classical.choice is
used: the comparison is the explicit S2101/S2096 comparison, and its
projections are prescribed by the pasted comparison cells. -/
noncomputable def S2121ChoiceFreeExtLiftToY
    (h : S2121ComparisonTwist f g T ptA Pg)
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
        (S2121D f g T ptA Pg).square1.toY) s.toY :=
  (S2121UpperComparison f g T ptA Pg h s).trans
    (S2121CanonicalComparison f g T ptA Pg s).symm

end Actual

/-! ## 3. The choice-free comparison has the prescribed projections -/

section Tools

/-- In a category, a morphism that is a right inverse of the hom of an iso is
the inverse of that iso. -/
theorem S2121EqInvOfCompHom {C : Type*} [Category C] {X Y : C} (e : Iso X Y)
    {g : Y ⟶ X} (h : g ≫ e.hom = 𝟙 Y) : g = e.inv := by
  calc g = g ≫ 𝟙 X := (Category.comp_id g).symm
    _ = g ≫ (e.hom ≫ e.inv) := by rw [Iso.hom_inv_id]
    _ = (g ≫ e.hom) ≫ e.inv := by rw [Category.assoc]
    _ = 𝟙 Y ≫ e.inv := by rw [h]
    _ = e.inv := Category.id_comp e.inv

end Tools

section WhiskerTools

variable {a b c : EtaleStackPseudofunctor S1726K}

/-- Composition of right whiskerings, in strong-transformation form. -/
theorem S2121STWhiskerRight_comp {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h)
    (i : b ⟶ c) :
    Pseudofunctor.StrongTrans.whiskerRight (η ≫ θ) i =
      Pseudofunctor.StrongTrans.whiskerRight η i ≫
        Pseudofunctor.StrongTrans.whiskerRight θ i :=
  Bicategory.comp_whiskerRight η θ i

/-- The inverse whiskering of an iso is the inverse of the whiskered iso. -/
theorem S2121STWhiskerRight_inv_of_hom_eq (f g : a ⟶ b) (k : b ⟶ c)
    (e : Iso f g) (θ : Iso (f ≫ k) (g ≫ k))
    (hθ : Pseudofunctor.StrongTrans.whiskerRight e.hom k = θ.hom) :
    Pseudofunctor.StrongTrans.whiskerRight e.inv k = θ.inv := by
  refine S2121EqInvOfCompHom θ ?_
  rw [← hθ]
  exact Bicategory.inv_hom_whiskerRight e k

end WhiskerTools

section ActualCompat

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable (T : SchemeOverField S1726K)
variable (ptA : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
variable (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))

theorem S2121UpperComparison_toA
    (h : S2121ComparisonTwist f g T ptA Pg)
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    Pseudofunctor.StrongTrans.whiskerRight
        (S2121UpperComparison f g T ptA Pg h s).hom (S2121D f g T ptA Pg).xi =
      (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom ≫
        ((S2076Witness (f := f) (g := g)).liftToX W
          (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)).inv :=
  S2121LiftUniq_of_projectionCompat_toA f g
    (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)
    (Pseudofunctor.StrongTrans.vcomp
      (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
      (S2121D f g T ptA Pg).toY1)
    (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
    (S2107LiftToYIsoY (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
    (S2115ProjectionCompat_of_twist f g
      (S2121ComparisonTwist_implies_twist f g T ptA Pg h s))

theorem S2121UpperComparison_toB
    (h : S2121ComparisonTwist f g T ptA Pg)
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    Pseudofunctor.StrongTrans.whiskerRight
        (S2121UpperComparison f g T ptA Pg h s).hom (S2121D f g T ptA Pg).toY2 =
      (S2107LiftToYIsoY (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom ≫
        ((S2076Witness (f := f) (g := g)).liftToY W
          (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)).inv :=
  S2121LiftUniq_of_projectionCompat_toB f g
    (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)
    (Pseudofunctor.StrongTrans.vcomp
      (S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
      (S2121D f g T ptA Pg).toY1)
    (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
    (S2107LiftToYIsoY (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s)
    (S2115ProjectionCompat_of_twist f g
      (S2121ComparisonTwist_implies_twist f g T ptA Pg h s))

theorem S2121CanonicalComparison_toA
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    Pseudofunctor.StrongTrans.whiskerRight
        (S2121CanonicalComparison f g T ptA Pg s).hom (S2121D f g T ptA Pg).xi =
      ((S2076Witness (f := f) (g := g)).liftToX W
        (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)).inv := by
  have hh := S2121LiftUniq_of_projectionCompat_toA f g
    (S2107Sq2ConeOf (S2121D f g T ptA Pg) s) (s.toY)
    (Iso.refl (Pseudofunctor.StrongTrans.vcomp s.toY (toA f g)))
    (Iso.refl (Pseudofunctor.StrongTrans.vcomp s.toY (toB f g)))
    (S2115ProjectionCompat_of_twist f g (S2121ReflTwist f g T ptA Pg s))
  rw [show (Iso.refl (Pseudofunctor.StrongTrans.vcomp s.toY (toA f g))).hom = 𝟙 _ from rfl,
    Category.id_comp] at hh
  exact hh

theorem S2121CanonicalComparison_toB
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    Pseudofunctor.StrongTrans.whiskerRight
        (S2121CanonicalComparison f g T ptA Pg s).hom (S2121D f g T ptA Pg).toY2 =
      ((S2076Witness (f := f) (g := g)).liftToY W
        (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)).inv := by
  have hh := S2121LiftUniq_of_projectionCompat_toB f g
    (S2107Sq2ConeOf (S2121D f g T ptA Pg) s) (s.toY)
    (Iso.refl (Pseudofunctor.StrongTrans.vcomp s.toY (toA f g)))
    (Iso.refl (Pseudofunctor.StrongTrans.vcomp s.toY (toB f g)))
    (S2115ProjectionCompat_of_twist f g (S2121ReflTwist f g T ptA Pg s))
  rw [show (Iso.refl (Pseudofunctor.StrongTrans.vcomp s.toY (toB f g))).hom = 𝟙 _ from rfl,
    Category.id_comp] at hh
  exact hh

theorem S2121CanonicalComparison_inv_toA
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    Pseudofunctor.StrongTrans.whiskerRight
        (S2121CanonicalComparison f g T ptA Pg s).inv (S2121D f g T ptA Pg).xi =
      ((S2076Witness (f := f) (g := g)).liftToX W
        (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)).hom := by
  exact S2121STWhiskerRight_inv_of_hom_eq s.toY
    ((S2076Witness (f := f) (g := g)).lift W
      (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)) (S2121D f g T ptA Pg).xi
    (S2121CanonicalComparison f g T ptA Pg s)
    (((S2076Witness (f := f) (g := g)).liftToX W
      (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)).symm)
    (S2121CanonicalComparison_toA f g T ptA Pg s)

theorem S2121CanonicalComparison_inv_toB
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    Pseudofunctor.StrongTrans.whiskerRight
        (S2121CanonicalComparison f g T ptA Pg s).inv (S2121D f g T ptA Pg).toY2 =
      ((S2076Witness (f := f) (g := g)).liftToY W
        (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)).hom := by
  exact S2121STWhiskerRight_inv_of_hom_eq s.toY
    ((S2076Witness (f := f) (g := g)).lift W
      (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)) (S2121D f g T ptA Pg).toY2
    (S2121CanonicalComparison f g T ptA Pg s)
    (((S2076Witness (f := f) (g := g)).liftToY W
      (S2107Sq2ConeOf (S2121D f g T ptA Pg) s)).symm)
    (S2121CanonicalComparison_toB f g T ptA Pg s)

theorem S2121ChoiceFreeExtLiftToY_toX
    (h : S2121ComparisonTwist f g T ptA Pg)
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    Pseudofunctor.StrongTrans.whiskerRight
        (S2121ChoiceFreeExtLiftToY f g T ptA Pg h s).hom
        (S2121D f g T ptA Pg).xi =
      (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom := by
  change Pseudofunctor.StrongTrans.whiskerRight
      ((S2121UpperComparison f g T ptA Pg h s).hom ≫
        (S2121CanonicalComparison f g T ptA Pg s).inv)
      (S2121D f g T ptA Pg).xi = _
  rw [S2121STWhiskerRight_comp, S2121UpperComparison_toA f g T ptA Pg h s,
    S2121CanonicalComparison_inv_toA f g T ptA Pg s]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem S2121ChoiceFreeExtLiftToY_toY
    (h : S2121ComparisonTwist f g T ptA Pg)
    {W : EtaleStackPseudofunctor S1726K}
    (s : (S2121D f g T ptA Pg).square1.Cone W) :
    Pseudofunctor.StrongTrans.whiskerRight
        (S2121ChoiceFreeExtLiftToY f g T ptA Pg h s).hom
        (S2121D f g T ptA Pg).toY2 =
      (S2107LiftToYIsoY (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom := by
  change Pseudofunctor.StrongTrans.whiskerRight
      ((S2121UpperComparison f g T ptA Pg h s).hom ≫
        (S2121CanonicalComparison f g T ptA Pg s).inv)
      (S2121D f g T ptA Pg).toY2 = _
  rw [S2121STWhiskerRight_comp, S2121UpperComparison_toB f g T ptA Pg h s,
    S2121CanonicalComparison_inv_toB f g T ptA Pg s]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The exact compatibility of the choice-free comparison.**  This is the
choice-free form of S2114ChosenComparisonCompat. -/
def S2121ChoiceFreeCompat (h : S2121ComparisonTwist f g T ptA Pg) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K)
    (s : (S2121D f g T ptA Pg).square1.Cone W),
    Pseudofunctor.StrongTrans.whiskerRight
        (S2121ChoiceFreeExtLiftToY f g T ptA Pg h s).hom
        (S2121D f g T ptA Pg).xi =
      (S2107LiftToYIsoX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom ∧
    Pseudofunctor.StrongTrans.whiskerRight
        (S2121ChoiceFreeExtLiftToY f g T ptA Pg h s).hom
        (S2121D f g T ptA Pg).toY2 =
      (S2107LiftToYIsoY (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) s).hom

theorem S2121ChoiceFreeCompat_holds
    (h : S2121ComparisonTwist f g T ptA Pg) :
    S2121ChoiceFreeCompat f g T ptA Pg h :=
  fun W s =>
    ⟨S2121ChoiceFreeExtLiftToY_toX f g T ptA Pg h s,
      S2121ChoiceFreeExtLiftToY_toY f g T ptA Pg h s⟩

end ActualCompat


/-! ## 4. The rebuilt lower witness and the remaining equation -/

section Rebuild

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable (T : SchemeOverField S1726K)
variable (ptA : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
variable (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))

/-- **The D.toY1 projection equation for the rebuilt comparison.**  The pasted
two-cell, whiskered along `D.toY1`, is the composite of the two choice-free
comparisons and `m.toY`.  This is the remaining equation (see the file
header); it is a named statement, not an axiom and not a sorry. -/
def S2121ToYEquation (h : S2121ComparisonTwist f g T ptA Pg) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K)
    (s t : (S2121D f g T ptA Pg).square1.Cone W)
    (m : (S2121D f g T ptA Pg).square1.ConeMorphism s t),
    Pseudofunctor.StrongTrans.whiskerRight
        (S2114PastedTwoCell f g T ptA Pg m)
        (S2121D f g T ptA Pg).square1.toY =
      (S2121ChoiceFreeExtLiftToY f g T ptA Pg h s).hom ≫ m.toY ≫
        (S2121ChoiceFreeExtLiftToY f g T ptA Pg h t).inv

/-- **The rebuilt lower witness.**  The lift and the first comparison are
S2107's canonical ones; the second comparison is the choice-free one.  Every
field is discharged except the `D.toY1` equation, which is the hypothesis
`hY`. -/
noncomputable def S2121RebuiltWitness
    (h : S2121ComparisonTwist f g T ptA Pg)
    (hY : S2121ToYEquation f g T ptA Pg h) :
    (S2121D f g T ptA Pg).square1.TwoPullbackWitness where
  lift W c := S2107ExtLift (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) c
  liftToX W c := S2107ExtLiftToX (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) c
  liftToY W c := S2121ChoiceFreeExtLiftToY f g T ptA Pg h c
  liftTwoCell W s t m := S2114PastedTwoCell f g T ptA Pg m
  liftTwoCell_toX W s t m := S2114PastedTwoCell_toX f g T ptA Pg m
  liftTwoCell_toY W s t m := hY W s t m
  twoCell_ext W first second alpha beta h1 h2 :=
    S2107Sq1TwoCellExt (S2121D f g T ptA Pg) (S2121WP f g T ptA Pg) alpha beta h1 h2

/-- **The actual butterfly assembly from the rebuilt witness.**  This is S2114's
assembly with the choice-free comparison in place of `S2107ExtLiftToY`. -/
noncomputable def S2121ToAWitness
    (h : S2121ComparisonTwist f g T ptA Pg)
    (hY : S2121ToYEquation f g T ptA Pg h) :
    (S2086ToASquare f g T ptA Pg).TwoPullbackWitness :=
  S2097SwapWitness (Pg.projectionMap.transformation) (S2086Lift f g T ptA Pg) (ptA)
    (toA f g) ((S2086LiftToA f g T ptA Pg).symm)
    (S2121RebuiltWitness f g T ptA Pg h hY)

end Rebuild

/-! ## 5. Checks and axiom audit -/

#check @S2121ChoiceFreeExtLiftToY
#check @S2121ChoiceFreeCompat
#check @S2121ChoiceFreeCompat_holds
#check @S2121RebuiltWitness
#check @S2121ToAWitness
#check @S2121ToYEquation
#check @S2121ComparisonTwist_of_concrete
#check @S2121ComparisonTwist_implies_twist

#print axioms S2121LiftUniq_of_projectionCompat_toA
#print axioms S2121LiftUniq_of_projectionCompat_toB
#print axioms S2121ReflTwist
#print axioms S2121ComparisonTwist_implies_twist
#print axioms S2121ChoiceFreeExtLiftToY
#print axioms S2121ChoiceFreeExtLiftToY_toX
#print axioms S2121ChoiceFreeExtLiftToY_toY
#print axioms S2121ChoiceFreeCompat_holds
#print axioms S2121RebuiltWitness
#print axioms S2121ToAWitness

end LeanFormal.IUT.XiFPaper.S2121ChoiceFreeLowerWitnessActual