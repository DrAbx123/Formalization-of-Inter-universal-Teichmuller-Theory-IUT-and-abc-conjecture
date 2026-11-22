/-
# S2123: the cone-category API of the strong presentation twist -- exact first missing

## The question

S2120 reduced the strong-presentation twist S2120StrongPresentationTwist to the
conjunction

  S2120FirstMissing = S2120PresentationLiftConeMor ∧ S2120PresentationTwoCellFull,

where

* (i) S2120PresentationLiftConeMor asks, for every strong presentation Pg, every cone s
  over the lower square and the transported cone
  c0 = S2118Conv f g T ptA Pg.toWeak s, for a cone morphism from the image cone of the
  presentation lift Pg.toWeak.isPullback.lift W c0 to c0;
* (ii) S2120PresentationTwoCellFull asks for the literal S1801 2-cell surjectivity
  S1801TwoCellSurjTo of the presentation witness Pg.toWeak.isPullback.

S2120 also recorded that the strong field S1852ConeEssSurj alone carries no information
at the twist data.  This file answers the remaining question: can (i) or (ii) be proved
for a strong presentation?

## The answer

**No proof of (i) or (ii) is obtained**, and no such proof is faked.  What is proved is
the exact cone-category API and its relation to the two S2120 components.

1. S2123LiftCoherentConeMor is the *coherent* lift cone morphism: a cone morphism from
   the image cone of the recorded lift whose two components are exactly the recorded
   comparisons w.liftToX W c and w.liftToY W c.  It is *equivalent to the twist*
   (S2123LiftCoherentConeMor_iff_twist) and it implies (i)
   (S2123LiftConeMor_of_coherent).  Hence the honest first missing datum is the coherent
   version of (i), which is the twist itself.

2. S2123LiftTwoCellFull is the 2-cell fullness **at the recorded lift only**: for every
   cone morphism m out of the image cone of w.lift W c there is a 2-cell
   u : w.lift W c ⟶ w.lift W c whose two whiskerings are the components of m composed
   with the inverse comparisons.  The literal (ii) implies it
   (S2123LiftTwoCellFull_of_twoCellSurjTo), but it quantifies over a single cone and a
   single 1-cell instead of all cones c' and all 1-cells f; it is a weakening of (ii).

3. S2123TwistAt_of_coneMor_and_liftTwoCellFull: **(i) plus 2-cell fullness at the
   recorded lift already force the twist.**  This sharpens
   S2120TwistAt_of_coneMor_and_twoCellFull, whose hypothesis is the full (ii) for an
   arbitrary cone c', an arbitrary 1-cell f and an arbitrary cone morphism m: the
   lift-restricted fullness is an instance of (ii), so (i) plus this instance is a
   weaker hypothesis.  Consequently the pair

     S2123ConeCategoryAPI := S2120LiftConeMor ∧ S2123LiftTwoCellFull

   suffices for the strong twist (S2123StrongPresentationTwist_of_coneCategoryAPI), and
   S2120's S2120FirstMissing implies this pair
   (S2123PresentationConeCategoryAPI_of_firstMissing).

4. S2123LiftConeMorAt_iff_residual: at a square whose second leg lands in a
   representable stack (the presentation square is such a square: its Y is the
   representable stack of the test scheme), the second component of *any* cone morphism
   out of the image cone is pinned to the recorded comparison
   (S2123ConeMorphism_toY_eq).  Hence (i) at a cone is *equivalent* to the existence of
   a single 2-cell a : (w.lift W c) ; sq.toX ⟶ c.toX whose whiskering along the base leg
   is the prescribed value.  In particular (i) does not assert that the recorded
   comparison liftToX is that 2-cell: it is a genuine 2-cell-lifting condition along the
   base leg, and the twist is the statement that liftToX itself is a solution.  For the
   presentation square the base leg is the cover map g.map; its 2-cell injectivity is
   not recorded by any cover axiom and is not a formal consequence of
   representability, so (i) does not formally give the twist.

5. S2123EssSurjAtLift_trivial, S2123EssSurjAtLift_of_essSurj, S2123EssSurjAtLift_unique:
   the strong field's instance at the recorded lift is the trivially true statement
   Nonempty (Iso (w.lift W c) (w.lift W c)), and *any* proof of it is propositionally
   equal to the unconditional trivial proof.  This is the formal content of "the strong
   field is vacuous at the twist data": the strong field produces *existence of
   2-isomorphisms* f ≅ w.lift W c, never an equation between the recorded comparison
   2-cells and the cone's structure cell.

## The exact first missing / required cone-category API

For a strong presentation Pg, the strong twist is equivalent to

  S2123PresentationLiftConeMorCoherent:
    for every cone s over the lower square, the pair of recorded comparisons
    (Pg.toWeak.isPullback.liftToX W c0, Pg.toWeak.isPullback.liftToY W c0) is a cone
    morphism imageCone (Pg.toWeak.isPullback.lift W c0) ⟶ c0

(S2123PresentationTwist_iff_liftConeMorCoherent).  Equivalently, it suffices to supply
(i) together with 2-cell fullness at the recorded lift
(S2123PresentationConeCategoryAPI), and this is weaker than S2120's S2120FirstMissing
because the second component is the lift instance of (ii) only.  Neither the coherent
cone morphism nor the lift-restricted fullness is obtained from Pg.coneEssSurj: the
strong field at the recorded lift is the trivially true S2123EssSurjAtLift.

## Honest boundary

(i) and (ii) are NOT proved, and no counterexample to either is constructed or
formalized inside the cover situation; this file proves the reduction, not the
independence of the missing datum from the strong field.  What is settled is:

* the strong twist is equivalent to the coherent lift cone morphism, i.e. to the pair
  of recorded comparisons being a cone morphism (S2123FirstMissing_characterisation);
* the existence form (i) is, at each cone, equivalent to a 2-cell lifting condition
  along the base leg whose canonical solution is exactly the twist
  (S2123LiftConeMorAt_iff_residual, S2123PresentationLiftConeMorAt_iff_residual);
* (i) together with 2-cell fullness at the recorded lift suffices for the strong twist
  (S2123StrongPresentationTwist_of_coneCategoryAPI), and the literal (ii) is stronger
  than that instance (S2123PresentationLiftTwoCellFull_of_twoCellFull);
* the strong field's lift-instance is the unconditionally true S2123EssSurjAtLift and
  every proof of it is the trivial one (S2123EssSurjAtLift_unique), hence the strong
  field cannot be the source of the comparison equation.

The remaining work is exactly one statement: the coherent lift cone morphism at the
presentation squares (equivalently S2118PresentationTwist, equivalently
S2120StrongPresentationTwist).  By contrast S2115 proves the corrected 2-cell fullness
for the iso-comma square from the twist, and S2104 records the canonical twist of the
actual butterfly lift at the fibre level; neither statement is at the presentation
square, and neither supplies the presentation comparison equation.

No sorry, no new axiom, no change of any recorded definition, no fabricated witness.
Axiom footprint: propext, Classical.choice, Quot.sound.
-/

import tmp.sheaf.xif.paper.S2120PresentationTwistActual
import tmp.sheaf.xif.paper.S2115UpperTwoCellFullActual
import tmp.sheaf.xif.paper.S2101SiteNaturalityActual
import tmp.sheaf.xif.paper.S2076IsoCommaTwoPullbackActual
import tmp.sheaf.xif.paper.S2110StrongTwoFullInputsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2123PresentationConeESActual

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
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2110StrongTwoFullInputsActual
open LeanFormal.IUT.XiFPaper.S2115UpperTwoCellFullActual
open LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual
open LeanFormal.IUT.XiFPaper.S2120PresentationTwistActual

universe u

/-! ## 1. The coherent lift cone morphism: the exact cone-category form of the twist -/

/-- **The coherent lift cone morphism.**  For every cone c there is a cone morphism
from the image cone of the recorded lift w.lift W c to c whose two components are
*exactly* the recorded comparisons w.liftToX W c and w.liftToY W c.

This is the coherent half of the cone-category essential surjectivity: unlike
S2120LiftConeMor, which only asks for *some* cone morphism, it pins the components to
the recorded comparisons.  It is therefore an equation of 2-cells, i.e. the twist. -/
def S2123LiftCoherentConeMor {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W),
    ∃ m : sq.ConeMorphism (S2107ImageCone sq (w.lift W c)) c,
      m.toX = (w.liftToX W c).hom ∧ m.toY = (w.liftToY W c).hom

/-- **The coherent lift cone morphism is exactly the twist.**  The two directions are
the compatibility equation of the cone morphism and the cone morphism built from the
recorded comparisons. -/
theorem S2123LiftCoherentConeMor_iff_twist
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) :
    S2123LiftCoherentConeMor sq w ↔
      ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W),
        Pseudofunctor.StrongTrans.whiskerRight (w.liftToX W c).hom sq.xToBase ≫
            c.commutes.hom =
          (S2107ImageCone sq (w.lift W c)).commutes.hom ≫
            Pseudofunctor.StrongTrans.whiskerRight (w.liftToY W c).hom sq.yToBase := by
  constructor
  · intro h W c
    obtain ⟨m, hmX, hmY⟩ := h W c
    rw [← hmX, ← hmY]
    exact m.compatibility
  · intro h W c
    exact ⟨{ toX := (w.liftToX W c).hom
             toY := (w.liftToY W c).hom
             compatibility := h W c }, rfl, rfl⟩

/-- **The coherent lift cone morphism implies the existence form (i).** -/
theorem S2123LiftConeMor_of_coherent
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (h : S2123LiftCoherentConeMor sq w) : S2120LiftConeMor sq w := by
  intro W c
  obtain ⟨m, -, -⟩ := h W c
  exact ⟨m⟩

/-! ## 2. The 2-cell fullness at the recorded lift only -/

/-- **2-cell fullness at the recorded lift only.**  For every cone morphism m out of
the image cone of the recorded lift, the two components of m are realised by a
2-cell u : w.lift W c ⟶ w.lift W c with the prescribed whiskerings.

This is the *only* instance of the literal S1801 TwoCellSurjTo that
S2120TwistAt_of_coneMor_and_twoCellFull uses: there c' is the image cone of
w.lift W c, f is w.lift W c and the two equalities are rfl.  Quantifying over just this
instance is therefore a weakening of (ii). -/
def S2123LiftTwoCellFull {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W)
    (m : sq.ConeMorphism (S2107ImageCone sq (w.lift W c)) c),
    ∃ u : w.lift W c ⟶ w.lift W c,
      Pseudofunctor.StrongTrans.whiskerRight u sq.toX =
          m.toX ≫ (w.liftToX W c).inv ∧
        Pseudofunctor.StrongTrans.whiskerRight u sq.toY =
          m.toY ≫ (w.liftToY W c).inv

/-- **The literal S1801 2-cell surjectivity implies the lift-restricted form.** -/
theorem S2123LiftTwoCellFull_of_twoCellSurjTo
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (h : S1801TwoCellSurjTo (F := S1726K) w) :
    S2123LiftTwoCellFull sq w := by
  intro W c m
  obtain ⟨u, huX, huY⟩ :=
    h W c (S2107ImageCone sq (w.lift W c)) (w.lift W c) m rfl rfl
  refine ⟨u, ?_, ?_⟩
  · simp only [eqToHom_refl, Category.id_comp] at huX
    exact huX
  · simp only [eqToHom_refl, Category.id_comp] at huY
    exact huY

/-! ## 3. The sharpened core theorem -/

/-- **The twist from a lift cone morphism and lift-restricted 2-cell fullness.**  This
is S2120TwistAt_of_coneMor_and_twoCellFull with the full S1801TwoCellSurjTo replaced by
its single lift instance S2123LiftTwoCellFull.

The representability hypothesis hsub ("all parallel 2-cells into the apex P are equal")
is automatic for the presentation square, whose apex is the representable stack
Y(Pg.pullbackScheme) (S1827SubsingletonModRep). -/
theorem S2123TwistAt_of_coneMor_and_liftTwoCellFull
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z)
    (w : sq.TwoPullbackWitness)
    (hsub : ∀ {W : EtaleStackPseudofunctor S1726K}
      (a b : Pseudofunctor.StrongTrans W P), Subsingleton (a ⟶ b))
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (hMor : Nonempty (sq.ConeMorphism (S2107ImageCone sq (w.lift W c)) c))
    (hFull : S2123LiftTwoCellFull sq w) :
    Pseudofunctor.StrongTrans.whiskerRight (w.liftToX W c).hom sq.xToBase ≫ c.commutes.hom =
      (S2107ImageCone sq (w.lift W c)).commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight (w.liftToY W c).hom sq.yToBase := by
  obtain ⟨m⟩ := hMor
  obtain ⟨u, huX, huY⟩ := hFull W c m
  have hu : u = 𝟙 (w.lift W c) :=
    @Subsingleton.elim _ (hsub (w.lift W c) (w.lift W c)) _ _
  have hXeq : m.toX = (w.liftToX W c).hom := by
    have h := huX
    rw [hu, S2120_whiskerRight_ident] at h
    exact S2120_eq_hom_of_comp_inv_eq_id m.toX (w.liftToX W c) h.symm
  have hYeq : m.toY = (w.liftToY W c).hom := by
    have h := huY
    rw [hu, S2120_whiskerRight_ident] at h
    exact S2120_eq_hom_of_comp_inv_eq_id m.toY (w.liftToY W c) h.symm
  rw [← hXeq, ← hYeq]
  exact m.compatibility

/-- The all-cones form of S2123TwistAt_of_coneMor_and_liftTwoCellFull. -/
theorem S2123Twist_of_liftConeMor_and_liftTwoCellFull
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (hsub : ∀ {W : EtaleStackPseudofunctor S1726K}
      (a b : Pseudofunctor.StrongTrans W P), Subsingleton (a ⟶ b))
    (hMor : S2120LiftConeMor sq w) (hFull : S2123LiftTwoCellFull sq w) :
    ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W),
      Pseudofunctor.StrongTrans.whiskerRight (w.liftToX W c).hom sq.xToBase ≫ c.commutes.hom =
        (S2107ImageCone sq (w.lift W c)).commutes.hom ≫
          Pseudofunctor.StrongTrans.whiskerRight (w.liftToY W c).hom sq.yToBase :=
  fun W c => S2123TwistAt_of_coneMor_and_liftTwoCellFull sq w hsub c (hMor W c) hFull

/-- **The cone-category API that suffices for the twist**: a cone morphism at the
recorded lift plus 2-cell fullness at the recorded lift.  This is weaker than S2120's
S2120ConeComparisonCoherent, which takes the full S1801TwoCellSurjTo. -/
def S2123ConeCategoryAPI {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) : Prop :=
  S2120LiftConeMor sq w ∧ S2123LiftTwoCellFull sq w

/-- S2120's cone-comparison datum implies the sharpened API. -/
theorem S2123ConeCategoryAPI_of_coherent
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (h : S2120ConeComparisonCoherent sq w) : S2123ConeCategoryAPI sq w :=
  ⟨h.1, S2123LiftTwoCellFull_of_twoCellSurjTo sq w h.2⟩

/-- The sharpened API gives the twist. -/
theorem S2123Twist_of_coneCategoryAPI
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (hsub : ∀ {W : EtaleStackPseudofunctor S1726K}
      (a b : Pseudofunctor.StrongTrans W P), Subsingleton (a ⟶ b))
    (h : S2123ConeCategoryAPI sq w) :
    ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W),
      Pseudofunctor.StrongTrans.whiskerRight (w.liftToX W c).hom sq.xToBase ≫ c.commutes.hom =
        (S2107ImageCone sq (w.lift W c)).commutes.hom ≫
          Pseudofunctor.StrongTrans.whiskerRight (w.liftToY W c).hom sq.yToBase :=
  S2123Twist_of_liftConeMor_and_liftTwoCellFull sq w hsub h.1 h.2

/-! ## 4. The presentation-level API -/

/-- **The coherent lift cone morphism at the presentation squares of strong
presentations.**  For every strong presentation Pg and every transported cone c0, the
recorded comparisons of Pg.toWeak.isPullback form a cone morphism
imageCone (lift W c0) ⟶ c0. -/
def S2123PresentationLiftConeMorCoherent : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg.toWeak).square1.Cone W),
    ∃ m : (S2118PresentationSquare f g T ptA Pg.toWeak).ConeMorphism
        (S2107ImageCone (S2118PresentationSquare f g T ptA Pg.toWeak)
          (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s)))
        (S2118Conv f g T ptA Pg.toWeak s),
      m.toX = (Pg.toWeak.isPullback.liftToX W
          (S2118Conv f g T ptA Pg.toWeak s)).hom ∧
        m.toY = (Pg.toWeak.isPullback.liftToY W
          (S2118Conv f g T ptA Pg.toWeak s)).hom

/-- **The strong twist is exactly the coherent lift cone morphism.** -/
theorem S2123PresentationTwist_iff_liftConeMorCoherent :
    S2123PresentationLiftConeMorCoherent ↔ S2120StrongPresentationTwist := by
  constructor
  · intro h A B C f g T ptA Pg W s
    obtain ⟨m, hmX, hmY⟩ := h A B C f g T ptA Pg W s
    dsimp only
    rw [← hmX, ← hmY]
    exact m.compatibility
  · intro h A B C f g T ptA Pg W s
    exact ⟨{ toX := (Pg.toWeak.isPullback.liftToX W
                (S2118Conv f g T ptA Pg.toWeak s)).hom
             toY := (Pg.toWeak.isPullback.liftToY W
                (S2118Conv f g T ptA Pg.toWeak s)).hom
             compatibility := h A B C f g T ptA Pg W s }, rfl, rfl⟩

/-- The coherent presentation API implies (i). -/
theorem S2123PresentationLiftConeMor_of_coherent
    (h : S2123PresentationLiftConeMorCoherent) : S2120PresentationLiftConeMor := by
  intro A B C f g T ptA Pg W s
  obtain ⟨m, -, -⟩ := h A B C f g T ptA Pg W s
  exact ⟨m⟩

/-- The strong twist implies the coherent presentation API. -/
theorem S2123PresentationLiftCoherent_of_strongTwist
    (h : S2120StrongPresentationTwist) : S2123PresentationLiftConeMorCoherent :=
  S2123PresentationTwist_iff_liftConeMorCoherent.mpr h

/-- S2120's S2120FirstMissing implies the coherent presentation API. -/
theorem S2123PresentationLiftCoherent_of_firstMissing
    (h : S2120FirstMissing) : S2123PresentationLiftConeMorCoherent :=
  S2123PresentationLiftCoherent_of_strongTwist
    (S2120StrongPresentationTwist_of_firstMissing h)

/-- **The lift-restricted 2-cell fullness at the presentation squares.** -/
def S2123PresentationLiftTwoCellFull : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)),
    S2123LiftTwoCellFull (S2118PresentationSquare f g T ptA Pg.toWeak)
      Pg.toWeak.isPullback

/-- The literal S2120 second missing datum (ii) implies the lift-restricted form. -/
theorem S2123PresentationLiftTwoCellFull_of_twoCellFull
    (h : S2120PresentationTwoCellFull) : S2123PresentationLiftTwoCellFull := by
  intro A B C f g T ptA Pg
  exact S2123LiftTwoCellFull_of_twoCellSurjTo _ _ (h A B C f g T ptA Pg)

/-- **The sharpened first-missing pair** at the presentation squares: (i) plus 2-cell
fullness at the recorded lift only.  It is implied by S2120's S2120FirstMissing, and it
suffices for the strong twist. -/
def S2123PresentationConeCategoryAPI : Prop :=
  S2120PresentationLiftConeMor ∧ S2123PresentationLiftTwoCellFull

/-- S2120's first missing implies the sharpened pair. -/
theorem S2123PresentationConeCategoryAPI_of_firstMissing
    (h : S2120FirstMissing) : S2123PresentationConeCategoryAPI :=
  ⟨h.1, S2123PresentationLiftTwoCellFull_of_twoCellFull h.2⟩

/-- **The sharpened pair gives the strong-presentation twist.** -/
theorem S2123StrongPresentationTwist_of_coneCategoryAPI
    (h : S2123PresentationConeCategoryAPI) : S2120StrongPresentationTwist := by
  intro A B C f g T ptA Pg W s
  exact S2123TwistAt_of_coneMor_and_liftTwoCellFull
    (S2118PresentationSquare f g T ptA Pg.toWeak) Pg.toWeak.isPullback
    (fun a b => S1827SubsingletonModRep a b)
    (S2118Conv f g T ptA Pg.toWeak s)
    (h.1 A B C f g T ptA Pg W s) (h.2 A B C f g T ptA Pg)

/-- S2120's first missing gives the strong twist through the sharpened pair; this is
the same conclusion as S2120StrongPresentationTwist_of_firstMissing, with the second
component of the hypothesis weakened to its lift instance. -/
theorem S2123StrongPresentationTwist_of_firstMissing_viaConeCategoryAPI
    (h : S2120FirstMissing) : S2120StrongPresentationTwist :=
  S2123StrongPresentationTwist_of_coneCategoryAPI
    (S2123PresentationConeCategoryAPI_of_firstMissing h)

/-- **Consumer form at S2110's strong input**, with the sharpened API in place of
S2120FirstMissing. -/
theorem S2123StrongPresentationTwist_for_strongTwoFullData
    (h : S2123PresentationConeCategoryAPI) (D : S2110StrongTwoFullData)
    (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA
      (D.strongPresentation A B C f g T ptA).toWeak).square1.Cone W) :
    let c0 := S2118Conv f g T ptA (D.strongPresentation A B C f g T ptA).toWeak s
    Pseudofunctor.StrongTrans.whiskerRight
        ((D.strongPresentation A B C f g T ptA).toWeak.isPullback.liftToX W c0).hom g.map ≫
        c0.commutes.hom =
      (S2107ImageCone (S2118PresentationSquare f g T ptA
          (D.strongPresentation A B C f g T ptA).toWeak)
          ((D.strongPresentation A B C f g T ptA).toWeak.isPullback.lift W c0)).commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight
          ((D.strongPresentation A B C f g T ptA).toWeak.isPullback.liftToY W c0).hom
          (Pseudofunctor.StrongTrans.vcomp ptA f.map) :=
  S2123StrongPresentationTwist_of_coneCategoryAPI h
    A B C f g T ptA (D.strongPresentation A B C f g T ptA) W s

/-- **Exact first missing, characterised.**  For strong presentations the strong twist
is equivalent to the coherent lift cone morphism, hence the exact required
cone-category API is the coherent version of (i); the pair (i) + (ii) of S2120 is
sufficient but its second component can be weakened to the lift instance. -/
theorem S2123FirstMissing_characterisation :
    S2120StrongPresentationTwist ↔ S2123PresentationLiftConeMorCoherent :=
  S2123PresentationTwist_iff_liftConeMorCoherent.symm

/-! ## 5. What the strong field does and does not supply at the recorded lift -/

/-- The restriction of the strong field to the recorded lift: for every cone c, the
1-cell w.lift W c with its recorded projections is 2-isomorphic to itself. -/
def S2123EssSurjAtLift {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp (w.lift W c) sq.toX) c.toX) →
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp (w.lift W c) sq.toY) c.toY) →
        Nonempty (Iso (w.lift W c) (w.lift W c))

/-- **The restriction is unconditionally true.**  At the recorded lift the strong
field's conclusion is inhabited with no hypothesis at all. -/
theorem S2123EssSurjAtLift_trivial {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) :
    S2123EssSurjAtLift sq w :=
  fun _ _ _ _ => ⟨Iso.refl _⟩

/-- The strong field implies its restriction to the recorded lift. -/
theorem S2123EssSurjAtLift_of_essSurj
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (h : S1801EssSurjOf S1726K sq w) : S2123EssSurjAtLift sq w := by
  intro W c hX hY
  exact h W c (w.lift W c) ⟨w.liftToX W c⟩ ⟨w.liftToY W c⟩

/-- **The restriction carries no data.**  Every proof of the strong field's
lift-instance is propositionally equal to the unconditional trivial proof; hence the
strong field cannot be the source of an equation between 2-cells at the recorded lift. -/
theorem S2123EssSurjAtLift_unique
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (h : S2123EssSurjAtLift sq w) :
    h = S2123EssSurjAtLift_trivial sq w :=
  Subsingleton.elim _ _

/-- The presentation-level form: the strong field at the recorded lift of a strong
presentation is the trivially true statement. -/
theorem S2123PresentationEssSurjAtLift_trivial
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)) :
    S2123EssSurjAtLift (S2118PresentationSquare f g T ptA Pg.toWeak)
      Pg.toWeak.isPullback :=
  S2123EssSurjAtLift_trivial _ _

/-- The strong presentation field, restricted to the recorded lift, is satisfied by the
trivial proof; this records the exact boundary at which the strong field stops carrying
information. -/
theorem S2123PresentationStrongFieldAtLift
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)) :
    S2123EssSurjAtLift (S2118PresentationSquare f g T ptA Pg.toWeak)
      Pg.toWeak.isPullback :=
  S2123EssSurjAtLift_of_essSurj _ _ Pg.coneEssSurj

/-! ## 6. The residual 2-cell lifting condition for (i) -/

/-- **The residual 2-cell lifting condition.**  A 2-cell
a : (w.lift W c) ; sq.toX ⟶ c.toX whose whiskering along the base leg is the value
prescribed by the cone morphism equation. -/
def S2123LiftToXCompatible {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (a : Pseudofunctor.StrongTrans.vcomp (w.lift W c) sq.toX ⟶ c.toX) : Prop :=
  Pseudofunctor.StrongTrans.whiskerRight a sq.xToBase ≫ c.commutes.hom =
    (S2107ImageCone sq (w.lift W c)).commutes.hom ≫
      Pseudofunctor.StrongTrans.whiskerRight (w.liftToY W c).hom sq.yToBase

/-- The residual condition unfolded. -/
theorem S2123LiftToXCompatible_iff
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (a : Pseudofunctor.StrongTrans.vcomp (w.lift W c) sq.toX ⟶ c.toX) :
    S2123LiftToXCompatible sq w c a ↔
      Pseudofunctor.StrongTrans.whiskerRight a sq.xToBase ≫ c.commutes.hom =
        (S2107ImageCone sq (w.lift W c)).commutes.hom ≫
          Pseudofunctor.StrongTrans.whiskerRight (w.liftToY W c).hom sq.yToBase :=
  Iff.rfl

/-- **The second component is pinned when the second leg lands in a representable
stack.**  Every cone morphism out of the image cone of the lift has
toY = (w.liftToY W c).hom. -/
theorem S2123ConeMorphism_toY_eq
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (hY : ∀ {W : EtaleStackPseudofunctor S1726K}
      (a b : Pseudofunctor.StrongTrans W Y), Subsingleton (a ⟶ b))
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (m : sq.ConeMorphism (S2107ImageCone sq (w.lift W c)) c) :
    m.toY = (w.liftToY W c).hom := by
  haveI : Subsingleton
      (Pseudofunctor.StrongTrans.vcomp (w.lift W c) sq.toY ⟶ c.toY) :=
    hY (Pseudofunctor.StrongTrans.vcomp (w.lift W c) sq.toY) c.toY
  exact Subsingleton.elim _ _

/-- **The exact content of (i) at one cone**: it is the existence of the residual
2-cell a, not the statement that the recorded comparison liftToX is such a 2-cell.  The
twist is the latter statement, which forces the canonical solution. -/
theorem S2123LiftConeMorAt_iff_residual
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (hY : ∀ {W : EtaleStackPseudofunctor S1726K}
      (a b : Pseudofunctor.StrongTrans W Y), Subsingleton (a ⟶ b))
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W) :
    Nonempty (sq.ConeMorphism (S2107ImageCone sq (w.lift W c)) c) ↔
      ∃ a : Pseudofunctor.StrongTrans.vcomp (w.lift W c) sq.toX ⟶ c.toX,
        S2123LiftToXCompatible sq w c a := by
  constructor
  · rintro ⟨m⟩
    refine ⟨m.toX, ?_⟩
    have hmY := S2123ConeMorphism_toY_eq sq w hY c m
    rw [S2123LiftToXCompatible_iff, ← hmY]
    exact m.compatibility
  · rintro ⟨a, ha⟩
    rw [S2123LiftToXCompatible_iff] at ha
    exact ⟨{ toX := a
             toY := (w.liftToY W c).hom
             compatibility := ha }⟩

/-- **At the presentation square the second component of any lift cone morphism is the
recorded comparison** (the second leg lands in the representable stack of the test
scheme). -/
theorem S2123PresentationConeMorphism_toY_eq
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg.toWeak).square1.Cone W)
    (m : (S2118PresentationSquare f g T ptA Pg.toWeak).ConeMorphism
      (S2107ImageCone (S2118PresentationSquare f g T ptA Pg.toWeak)
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s)))
      (S2118Conv f g T ptA Pg.toWeak s)) :
    m.toY = (Pg.toWeak.isPullback.liftToY W
      (S2118Conv f g T ptA Pg.toWeak s)).hom :=
  S2123ConeMorphism_toY_eq (S2118PresentationSquare f g T ptA Pg.toWeak)
    Pg.toWeak.isPullback (fun a b => S1827SubsingletonModRep a b) _ m

/-- **At the presentation square, (i) at one transported cone is exactly the residual
2-cell lifting condition along the base leg g.map.** -/
theorem S2123PresentationLiftConeMorAt_iff_residual
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg.toWeak).square1.Cone W) :
    Nonempty ((S2118PresentationSquare f g T ptA Pg.toWeak).ConeMorphism
      (S2107ImageCone (S2118PresentationSquare f g T ptA Pg.toWeak)
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s)))
      (S2118Conv f g T ptA Pg.toWeak s)) ↔
      ∃ a : Pseudofunctor.StrongTrans.vcomp
            (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))
            (S2118PresentationSquare f g T ptA Pg.toWeak).toX ⟶
          (S2118Conv f g T ptA Pg.toWeak s).toX,
        S2123LiftToXCompatible (S2118PresentationSquare f g T ptA Pg.toWeak)
          Pg.toWeak.isPullback (S2118Conv f g T ptA Pg.toWeak s) a :=
  S2123LiftConeMorAt_iff_residual _ _ (fun a b => S1827SubsingletonModRep a b) _

/-! ## 7. Checks and axiom audit -/

#check @S2123LiftCoherentConeMor
#check @S2123LiftCoherentConeMor_iff_twist
#check @S2123LiftConeMor_of_coherent
#check @S2123LiftTwoCellFull
#check @S2123LiftTwoCellFull_of_twoCellSurjTo
#check @S2123TwistAt_of_coneMor_and_liftTwoCellFull
#check @S2123Twist_of_liftConeMor_and_liftTwoCellFull
#check @S2123ConeCategoryAPI
#check @S2123ConeCategoryAPI_of_coherent
#check @S2123Twist_of_coneCategoryAPI
#check S2123PresentationLiftConeMorCoherent
#check S2123PresentationTwist_iff_liftConeMorCoherent
#check S2123PresentationLiftConeMor_of_coherent
#check S2123PresentationLiftCoherent_of_strongTwist
#check S2123PresentationLiftCoherent_of_firstMissing
#check S2123PresentationLiftTwoCellFull
#check S2123PresentationLiftTwoCellFull_of_twoCellFull
#check S2123PresentationConeCategoryAPI
#check S2123PresentationConeCategoryAPI_of_firstMissing
#check S2123StrongPresentationTwist_of_coneCategoryAPI
#check S2123StrongPresentationTwist_of_firstMissing_viaConeCategoryAPI
#check S2123StrongPresentationTwist_for_strongTwoFullData
#check S2123FirstMissing_characterisation
#check @S2123EssSurjAtLift
#check @S2123EssSurjAtLift_trivial
#check @S2123EssSurjAtLift_of_essSurj
#check @S2123EssSurjAtLift_unique
#check S2123PresentationEssSurjAtLift_trivial
#check S2123PresentationStrongFieldAtLift
#check @S2123LiftToXCompatible
#check @S2123LiftToXCompatible_iff
#check @S2123ConeMorphism_toY_eq
#check @S2123LiftConeMorAt_iff_residual
#check S2123PresentationConeMorphism_toY_eq
#check S2123PresentationLiftConeMorAt_iff_residual

#print axioms S2123LiftCoherentConeMor_iff_twist
#print axioms S2123LiftConeMor_of_coherent
#print axioms S2123LiftTwoCellFull_of_twoCellSurjTo
#print axioms S2123TwistAt_of_coneMor_and_liftTwoCellFull
#print axioms S2123Twist_of_liftConeMor_and_liftTwoCellFull
#print axioms S2123ConeCategoryAPI_of_coherent
#print axioms S2123Twist_of_coneCategoryAPI
#print axioms S2123PresentationTwist_iff_liftConeMorCoherent
#print axioms S2123PresentationLiftConeMor_of_coherent
#print axioms S2123PresentationLiftCoherent_of_strongTwist
#print axioms S2123PresentationLiftCoherent_of_firstMissing
#print axioms S2123PresentationLiftTwoCellFull_of_twoCellFull
#print axioms S2123PresentationConeCategoryAPI_of_firstMissing
#print axioms S2123StrongPresentationTwist_of_coneCategoryAPI
#print axioms S2123StrongPresentationTwist_of_firstMissing_viaConeCategoryAPI
#print axioms S2123StrongPresentationTwist_for_strongTwoFullData
#print axioms S2123FirstMissing_characterisation
#print axioms S2123EssSurjAtLift_trivial
#print axioms S2123EssSurjAtLift_of_essSurj
#print axioms S2123EssSurjAtLift_unique
#print axioms S2123PresentationEssSurjAtLift_trivial
#print axioms S2123PresentationStrongFieldAtLift
#print axioms S2123LiftToXCompatible_iff
#print axioms S2123ConeMorphism_toY_eq
#print axioms S2123LiftConeMorAt_iff_residual
#print axioms S2123PresentationConeMorphism_toY_eq
#print axioms S2123PresentationLiftConeMorAt_iff_residual

end LeanFormal.IUT.XiFPaper.S2123PresentationConeESActual
