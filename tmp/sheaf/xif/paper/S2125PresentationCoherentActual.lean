/-
# S2125: the strong-presentation coherent lift cone morphism is not derived from
# the strong field; the exact fibre-level 2-cell API

## The question

S2123 reduced the strong-presentation twist to

  S2123PresentationLiftConeMorCoherent:

for every strong presentation Pg and every transported cone c0 over the
presentation square, the *recorded* comparisons

  (Pg.toWeak.isPullback.liftToX W c0, Pg.toWeak.isPullback.liftToY W c0)

are the two components of a cone morphism from the image cone of the recorded
lift to c0.  S2123 proved that this statement is equivalent to
S2120StrongPresentationTwist (and to S2118PresentationTwist at Pg.toWeak),
and that the strong field Pg.coneEssSurj is vacuous at the recorded lift.

The present file attacks the target directly.  A direct proof from the recorded
data fails for a structural reason, recorded formally below: the strong field
at the recorded lift has conclusion type Nonempty (Iso l l), which is a
subsingleton because the presentation apex is representable; every proof of it
is the trivial proof (S2125PresentationStrongFieldAtLift_eq_refl) and it does
not depend on the comparison isomorphisms (S2125PresentationStrongFieldAtLift_indep).
The recorded witness fields only turn cone morphisms into 2-cells on lifts
(liftTwoCell); they never produce a cone morphism out of the image cone, which
is what the target asks for.  S2115's corrected fullness is a theorem about the
actual iso-comma square S2076Square (whose witness and structure cell are
concrete), and S2104's canonical twist is the fibre-level twist of the butterfly
lift; neither statement is the presentation square, whose comparisons are
arbitrary fields of Pg.toWeak.isPullback.  Hence the result of the attempt is:

* the target is **not proved** and no witness is fabricated; what is proved is
  the exact fibre-level form of the missing 2-cell equation, and the precise
  sense in which the strong field cannot supply it;

* the missing equation is reduced to a single equation in the target fibre
  category C.source.fiber at every test object U and every apex object x,
  involving only the recorded comparisons, the cone's structure cell, and the
  square's own structure cell Pg.commutes at the lift object
  (S2125PresentationConcreteTwist, S2125PresentationConcreteTwistAt);

* this displayed equation is *exactly* the compatibility of the recorded
  comparison liftToX, not merely the existence of some 2-cell
  (S2125PresentationRecordedComparison_iff).  The existence form is the
  residual S2120 datum S2120PresentationLiftConeMor
  (S2125PresentationRequiredTwoCellAPI_iff_liftConeMor), and it is strictly
  weaker: S2123's S2123LiftTwoCellFull is needed to turn an arbitrary
  residual 2-cell into the recorded one;

* the strong field's output at the recorded lift is literally
  the trivial proof, and is independent of the comparison isomorphisms fed to
  it (S2125PresentationStrongFieldAtLift_eq_refl,
  S2125PresentationStrongFieldAtLift_indep).  Its conclusion type is a
  subsingleton, so it cannot carry an equation between the comparison 2-cells.
  More structurally, its whole statement is definitionally a property of the
  lift function alone: S2125EssSurjOf_iff_strongFieldOfLift and
  S2125PresentationConeEssSurj_iff_strongFieldOfLift contain no recorded
  comparison at all.

## What is proved

1. S2125TwistAt is the twist at one cone; S2125DisplayedTwistAt is its
   componentwise form at every (U,x); S2125ConcreteTwistAt replaces the
   image-cone structure cell by sq.commutes at the lift object, using
   S2125ImageCone_commutes_app.  These three are proved equivalent
   (S2125TwistAt_iff_displayed, S2125DisplayedTwistAt_iff_concrete).

1bis. S2125StrongFieldOfLift isolates the strong field as a property of the lift
   function alone; S2125EssSurjOf_iff_strongFieldOfLift and
   S2125PresentationConeEssSurj_iff_strongFieldOfLift are definitional
   identifications showing that no recorded comparison occurs in the strong
   field's statement.

2. S2125ImageCone_commutes_app: the structure cell of the S2107 image cone at
   (U,x) is the structure cell of the square at the lift object
   ((u.app U).toFunctor.obj x).  This is the general form of S2115's
   computation for the iso-comma square, and it is what makes the presentation
   equation concrete.

3. S2125PresentationConcreteTwist: the exact API, componentwise over the
   presentation squares of strong presentations.  It is equivalent to
   S2123PresentationLiftConeMorCoherent and to
   S2120StrongPresentationTwist
   (S2125PresentationConcreteTwist_iff_coherent,
   S2125PresentationConcreteTwist_iff_strongTwist).

4. S2125PresentationRequiredTwoCellAPI: the residual existence form (a 2-cell
   a along the source leg with the prescribed whiskering).  It is proved
   equivalent to S2120PresentationLiftConeMor
   (S2125PresentationRequiredTwoCellAPI_iff_liftConeMor), and the recorded
   comparison is a solution precisely in the coherent case
   (S2125PresentationRecordedComparison_iff).

5. Consequences: the concrete twist follows from S2118PresentationTwist,
   from S2120's S2120FirstMissing, and from S2123's cone-category API
   (S2125PresentationConcreteTwist_of_S2118,
   ..._of_firstMissing, ..._of_coneCategoryAPI); conversely it gives the
   strong twist.

## Honest boundary

S2123PresentationLiftConeMorCoherent is **not** proved.  The strong field is
not used in the reduction, and at the recorded lift it is provably the
trivial proof; the missing datum is the single fibre equation displayed in
S2125PresentationConcreteTwist (equivalently the compatible recorded
comparison of S2125PresentationRecordedComparison_iff).  No sorry, no new
axiom, no change of any definition, no fabricated 2-cell.  Axiom footprint:
propext, Classical.choice, Quot.sound.
-/

import tmp.sheaf.xif.paper.S2123PresentationConeESActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2125PresentationCoherentActual

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
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2110StrongTwoFullInputsActual
open LeanFormal.IUT.XiFPaper.S2115UpperTwoCellFullActual
open LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual
open LeanFormal.IUT.XiFPaper.S2120PresentationTwistActual
open LeanFormal.IUT.XiFPaper.S2123PresentationConeESActual

universe u

/-! ## 1. The twist and its fibre-level form -/

section Generic

variable {P X Y Z : EtaleStackPseudofunctor S1726K}
variable (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
variable {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)

/-- The twist at one cone: the recorded comparisons are a cone morphism from the
image cone of the recorded lift to c.  This is exactly the body of the twist
in S2123LiftCoherentConeMor_iff_twist. -/
def S2125TwistAt : Prop :=
  Pseudofunctor.StrongTrans.whiskerRight (w.liftToX W c).hom sq.xToBase ≫ c.commutes.hom =
    (S2107ImageCone sq (w.lift W c)).commutes.hom ≫
      Pseudofunctor.StrongTrans.whiskerRight (w.liftToY W c).hom sq.yToBase

/-- The displayed fibre-level form of the twist: at every test object U and
every apex object x, the equation of morphisms in the target fibre. -/
def S2125DisplayedTwistAt : Prop :=
  ∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(W.obj U)),
    (sq.xToBase.app U).toFunctor.map (((w.liftToX W c).hom.as.app U).toNatTrans.app x) ≫
        (c.commutes.hom.as.app U).toNatTrans.app x =
      ((S2107ImageCone sq (w.lift W c)).commutes.hom.as.app U).toNatTrans.app x ≫
        (sq.yToBase.app U).toFunctor.map (((w.liftToY W c).hom.as.app U).toNatTrans.app x)

/-- The concrete fibre-level form of the twist: the image-cone structure cell is
replaced by the square's own structure cell at the lift object.  This is the
form in which the missing equation can be checked in the geometry. -/
def S2125ConcreteTwistAt : Prop :=
  ∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(W.obj U)),
    (sq.xToBase.app U).toFunctor.map (((w.liftToX W c).hom.as.app U).toNatTrans.app x) ≫
        (c.commutes.hom.as.app U).toNatTrans.app x =
      (sq.commutes.hom.as.app U).toNatTrans.app
          (((w.lift W c).app U).toFunctor.obj x) ≫
        (sq.yToBase.app U).toFunctor.map (((w.liftToY W c).hom.as.app U).toNatTrans.app x)

/-- **The structure cell of the image cone is the structure cell of the square at
the lift object.**  This is the general form of S2115's iso-comma computation,
for an arbitrary square and an arbitrary 1-cell u. -/
theorem S2125ImageCone_commutes_app
    (u : Pseudofunctor.StrongTrans W P)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(W.obj U)) :
    ((S2107ImageCone sq u).commutes.hom.as.app U).toNatTrans.app x =
      (sq.commutes.hom.as.app U).toNatTrans.app ((u.app U).toFunctor.obj x) := by
  change ((S2058AssociatorIso u sq.toX sq.xToBase).hom.as.app U).toNatTrans.app x ≫
      ((S2058WhiskerLeftIso u (sq.toX.vcomp sq.xToBase) (sq.toY.vcomp sq.yToBase)
        sq.commutes).hom.as.app U).toNatTrans.app x ≫
        ((S2058AssociatorIso u sq.toY sq.yToBase).symm.hom.as.app U).toNatTrans.app x =
    (sq.commutes.hom.as.app U).toNatTrans.app ((u.app U).toFunctor.obj x)
  have hA : ((S2058AssociatorIso u sq.toX sq.xToBase).hom.as.app U).toNatTrans.app x = 𝟙 _ := by
    change (α_ (u.app U) (sq.toX.app U) (sq.xToBase.app U)).hom.toNatTrans.app x = _
    rw [Cat.associator_hom_app]
    rfl
  have hC : ((S2058AssociatorIso u sq.toY sq.yToBase).symm.hom.as.app U).toNatTrans.app x = 𝟙 _ := by
    change (α_ (u.app U) (sq.toY.app U) (sq.yToBase.app U)).inv.toNatTrans.app x = _
    rw [Cat.associator_inv_app]
    rfl
  have hM : ((S2058WhiskerLeftIso u (sq.toX.vcomp sq.xToBase) (sq.toY.vcomp sq.yToBase)
        sq.commutes).hom.as.app U).toNatTrans.app x =
      (sq.commutes.hom.as.app U).toNatTrans.app ((u.app U).toFunctor.obj x) := by
    rw [S2058WhiskerLeftIso_hom]
    change (Functor.whiskerLeft (u.app U).toFunctor
      (sq.commutes.hom.as.app U).toNatTrans).app x = _
    rw [Functor.whiskerLeft_app]
  rw [hA, hC, hM]
  simp only [Category.id_comp, Category.comp_id]

/-- The twist equals its displayed fibre-level form. -/
theorem S2125TwistAt_iff_displayed : S2125TwistAt sq w c ↔ S2125DisplayedTwistAt sq w c := by
  have hcomp : ∀ {F G : EtaleStackPseudofunctor S1726K}
      {a b d : Pseudofunctor.StrongTrans F G} (g1 : a ⟶ b) (g2 : b ⟶ d),
      (g1 ≫ g2).as = Pseudofunctor.StrongTrans.Modification.vcomp g1.as g2.as :=
    fun _ _ => rfl
  constructor
  · intro h U x
    have hh := congrArg (fun m => (m.as.app U).toNatTrans.app x) h
    simpa only [hcomp, Pseudofunctor.StrongTrans.Modification.vcomp_app, Cat.Hom₂.comp_app,
      Pseudofunctor.StrongTrans.whiskerRight_as_app, Cat.whiskerRight_app] using hh
  · intro h
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro U
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    have hh := h U x
    simpa only [hcomp, Pseudofunctor.StrongTrans.Modification.vcomp_app, Cat.Hom₂.comp_app,
      Pseudofunctor.StrongTrans.whiskerRight_as_app, Cat.whiskerRight_app] using hh

/-- The displayed form equals the concrete form. -/
theorem S2125DisplayedTwistAt_iff_concrete :
    S2125DisplayedTwistAt sq w c ↔ S2125ConcreteTwistAt sq w c := by
  constructor
  · intro h U x
    have hh := h U x
    rw [S2125ImageCone_commutes_app sq (w.lift W c) U x] at hh
    exact hh
  · intro h U x
    have hh := h U x
    rw [S2125ImageCone_commutes_app sq (w.lift W c) U x]
    exact hh

/-- The twist in concrete fibre form. -/
theorem S2125TwistAt_iff_concrete : S2125TwistAt sq w c ↔ S2125ConcreteTwistAt sq w c :=
  (S2125TwistAt_iff_displayed sq w c).trans (S2125DisplayedTwistAt_iff_concrete sq w c)

/-- The recorded comparison is a solution of the residual equation exactly when
the twist holds. -/
theorem S2125LiftToXCompatible_recorded_iff :
    S2123LiftToXCompatible sq w c (w.liftToX W c).hom ↔ S2125TwistAt sq w c :=
  Iff.rfl

end Generic

/-! ## 1bis. The strong field is a property of the lift alone -/

/-- The strong field isolated as a property of the lift function only.  The
definition mentions no comparison isomorphism: the hypotheses of the cone
comparison are arbitrary isomorphisms fed to it, and the conclusion refers only
to the lift. -/
def S2125StrongFieldOfLift {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z)
    (L : ∀ (W : EtaleStackPseudofunctor S1726K), sq.Cone W →
      Pseudofunctor.StrongTrans W P) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W)
    (f : Pseudofunctor.StrongTrans W P),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toX) c.toX) →
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toY) c.toY) →
        Nonempty (Iso f (L W c))

/-- The recorded strong field is definitionally the lift-only property. -/
theorem S2125EssSurjOf_iff_strongFieldOfLift
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) :
    S1827EssSurjOf sq w ↔ S2125StrongFieldOfLift sq w.lift :=
  Iff.rfl

/-- The lift-only property depends only on the lift function. -/
theorem S2125StrongFieldOfLift_congr
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z)
    {L L' : (W : EtaleStackPseudofunctor S1726K) → sq.Cone W →
      Pseudofunctor.StrongTrans W P}
    (h : L = L') : S2125StrongFieldOfLift sq L ↔ S2125StrongFieldOfLift sq L' := by
  rw [h]

/-- The strong presentation field of a presentation square is definitionally the
lift-only property: no recorded comparison occurs in its statement. -/
theorem S2125PresentationConeEssSurj_iff_strongFieldOfLift
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)) :
    S1852ConeEssSurj Pg.toWeak ↔
      S2125StrongFieldOfLift (S2118PresentationSquare f g T ptA Pg.toWeak)
        Pg.toWeak.isPullback.lift :=
  Iff.rfl

/-! ## 2. The exact presentation-level API -/

/-- **The exact fibre-level 2-cell API at the presentation squares.**  For every
strong presentation Pg, every transported cone c0, every test object U and
every apex object x, the recorded comparisons satisfy the concrete comparison
equation in C.source.fiber at U. -/
def S2125PresentationConcreteTwist : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg.toWeak).square1.Cone W),
    S2125ConcreteTwistAt (S2118PresentationSquare f g T ptA Pg.toWeak)
      Pg.toWeak.isPullback (S2118Conv f g T ptA Pg.toWeak s)

/-- **The explicit component form of the presentation API.**  This is the
componentwise equation involving only Pg.commutes, the structure cell of the
transported cone, and the recorded comparisons. -/
theorem S2125PresentationConcreteTwistAt_iff_explicit :
    S2125PresentationConcreteTwist ↔
      ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
        (T : SchemeOverField S1726K)
        (ptA : Pseudofunctor.StrongTrans
          (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
        (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
        (W : EtaleStackPseudofunctor S1726K)
        (s : (S2097Pasting f g T ptA Pg.toWeak).square1.Cone W)
        (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(W.obj U)),
        (g.map.app U).toFunctor.map
            (((Pg.toWeak.isPullback.liftToX W
              (S2118Conv f g T ptA Pg.toWeak s)).hom.as.app U).toNatTrans.app x) ≫
          ((S2118Conv f g T ptA Pg.toWeak s).commutes.hom.as.app U).toNatTrans.app x =
        (Pg.toWeak.commutes.hom.as.app U).toNatTrans.app
            (((Pg.toWeak.isPullback.lift W
              (S2118Conv f g T ptA Pg.toWeak s)).app U).toFunctor.obj x) ≫
          ((Pseudofunctor.StrongTrans.vcomp ptA f.map).app U).toFunctor.map
            (((Pg.toWeak.isPullback.liftToY W
              (S2118Conv f g T ptA Pg.toWeak s)).hom.as.app U).toNatTrans.app x) :=
  Iff.rfl

/-- The concrete API is the twist at the presentation squares. -/
theorem S2125PresentationConcreteTwist_iff_coherent :
    S2125PresentationConcreteTwist ↔ S2123PresentationLiftConeMorCoherent := by
  constructor
  · intro h
    refine S2123PresentationLiftCoherent_of_strongTwist ?_
    intro A B C f g T ptA Pg W s
    exact (S2125TwistAt_iff_concrete
      (S2118PresentationSquare f g T ptA Pg.toWeak)
      Pg.toWeak.isPullback (S2118Conv f g T ptA Pg.toWeak s)).mpr
      (h A B C f g T ptA Pg W s)
  · intro h A B C f g T ptA Pg W s
    exact (S2125TwistAt_iff_concrete
      (S2118PresentationSquare f g T ptA Pg.toWeak)
      Pg.toWeak.isPullback (S2118Conv f g T ptA Pg.toWeak s)).mp
      ((S2123PresentationTwist_iff_liftConeMorCoherent.mp h)
        A B C f g T ptA Pg W s)

/-- The concrete API is exactly the strong-presentation twist. -/
theorem S2125PresentationConcreteTwist_iff_strongTwist :
    S2125PresentationConcreteTwist ↔ S2120StrongPresentationTwist :=
  S2125PresentationConcreteTwist_iff_coherent.trans
    S2123PresentationTwist_iff_liftConeMorCoherent

/-- **The recorded comparison is compatible exactly in the coherent case.**  The
presentation-level form: the required 2-cell equation for the recorded
comparison liftToX holds for all strong presentations and cones iff
S2123PresentationLiftConeMorCoherent. -/
theorem S2125PresentationRecordedComparison_iff :
    (∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
      (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
      (W : EtaleStackPseudofunctor S1726K)
      (s : (S2097Pasting f g T ptA Pg.toWeak).square1.Cone W),
      S2123LiftToXCompatible (S2118PresentationSquare f g T ptA Pg.toWeak)
        Pg.toWeak.isPullback (S2118Conv f g T ptA Pg.toWeak s)
        (Pg.toWeak.isPullback.liftToX W
          (S2118Conv f g T ptA Pg.toWeak s)).hom) ↔
      S2123PresentationLiftConeMorCoherent := by
  constructor
  · intro h
    refine S2125PresentationConcreteTwist_iff_coherent.mp ?_
    intro A B C f g T ptA Pg W s
    exact (S2125TwistAt_iff_concrete
      (S2118PresentationSquare f g T ptA Pg.toWeak)
      Pg.toWeak.isPullback (S2118Conv f g T ptA Pg.toWeak s)).mp
      ((S2125LiftToXCompatible_recorded_iff
        (S2118PresentationSquare f g T ptA Pg.toWeak)
        Pg.toWeak.isPullback (S2118Conv f g T ptA Pg.toWeak s)).mp
        (h A B C f g T ptA Pg W s))
  · intro h A B C f g T ptA Pg W s
    have hconc := S2125PresentationConcreteTwist_iff_coherent.mpr h
    have htw : S2125TwistAt (S2118PresentationSquare f g T ptA Pg.toWeak)
        Pg.toWeak.isPullback (S2118Conv f g T ptA Pg.toWeak s) :=
      (S2125TwistAt_iff_concrete
        (S2118PresentationSquare f g T ptA Pg.toWeak)
        Pg.toWeak.isPullback (S2118Conv f g T ptA Pg.toWeak s)).mpr
        (hconc A B C f g T ptA Pg W s)
    exact (S2125LiftToXCompatible_recorded_iff
      (S2118PresentationSquare f g T ptA Pg.toWeak)
      Pg.toWeak.isPullback (S2118Conv f g T ptA Pg.toWeak s)).mpr htw

/-! ## 3. The residual 2-cell existence form -/

/-- **The required residual 2-cell API**: for every strong presentation and every
transported cone there exists a 2-cell a along the source leg satisfying the
prescribed whiskering equation.  This is the S2120 existence form at the
presentation squares. -/
def S2125PresentationRequiredTwoCellAPI : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg.toWeak).square1.Cone W),
    ∃ a : Pseudofunctor.StrongTrans.vcomp
          (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))
          (S2118PresentationSquare f g T ptA Pg.toWeak).toX ⟶
        (S2118Conv f g T ptA Pg.toWeak s).toX,
      S2123LiftToXCompatible (S2118PresentationSquare f g T ptA Pg.toWeak)
        Pg.toWeak.isPullback (S2118Conv f g T ptA Pg.toWeak s) a

/-- The residual existence form is exactly S2120's first missing cone
morphism. -/
theorem S2125PresentationRequiredTwoCellAPI_iff_liftConeMor :
    S2125PresentationRequiredTwoCellAPI ↔ S2120PresentationLiftConeMor := by
  constructor
  · intro h A B C f g T ptA Pg W s
    exact (S2123PresentationLiftConeMorAt_iff_residual
      (f := f) (g := g) (T := T) (ptA := ptA) (Pg := Pg) (W := W) (s := s)).mpr
      (h A B C f g T ptA Pg W s)
  · intro h A B C f g T ptA Pg W s
    exact (S2123PresentationLiftConeMorAt_iff_residual
      (f := f) (g := g) (T := T) (ptA := ptA) (Pg := Pg) (W := W) (s := s)).mp
      (h A B C f g T ptA Pg W s)

/-- The coherent form gives the residual existence form. -/
theorem S2125PresentationRequiredTwoCellAPI_of_coherent
    (h : S2123PresentationLiftConeMorCoherent) : S2125PresentationRequiredTwoCellAPI :=
  S2125PresentationRequiredTwoCellAPI_iff_liftConeMor.mpr
    (S2123PresentationLiftConeMor_of_coherent h)

/-- **The sufficient cone-category API.**  The residual existence form together
with S2123's 2-cell fullness at the recorded lift gives the concrete API.  This
is the precise two-input form of the missing datum: the existence of a residual
2-cell plus the fullness that forces it to be the recorded comparison. -/
theorem S2125PresentationConcreteTwist_of_requiredAndFull
    (h : S2125PresentationRequiredTwoCellAPI)
    (hfull : S2123PresentationLiftTwoCellFull) : S2125PresentationConcreteTwist :=
  S2125PresentationConcreteTwist_iff_strongTwist.mpr
    (S2123StrongPresentationTwist_of_coneCategoryAPI
      ⟨S2125PresentationRequiredTwoCellAPI_iff_liftConeMor.mp h, hfull⟩)

/-! ## 3bis. Summary: exact first missing and sufficient API -/

/-- **Exact first missing, characterised.**  The target is equivalent to the
explicit fibre-level comparison equation of S2125PresentationConcreteTwist. -/
theorem S2125ExactFirstMissing :
    S2123PresentationLiftConeMorCoherent ↔ S2125PresentationConcreteTwist :=
  S2125PresentationConcreteTwist_iff_coherent.symm

/-- **The sufficient cone-category API gives the target**: a residual 2-cell at
every transported cone plus 2-cell fullness at the recorded lift. -/
theorem S2125SufficientAPI
    (h : S2125PresentationRequiredTwoCellAPI)
    (hfull : S2123PresentationLiftTwoCellFull) :
    S2123PresentationLiftConeMorCoherent :=
  S2125PresentationConcreteTwist_iff_coherent.mp
    (S2125PresentationConcreteTwist_of_requiredAndFull h hfull)

/-! ## 4. What the strong field supplies at the recorded lift -/

/-- **The strong field's conclusion at the recorded lift is the trivial proof.**
The conclusion type is Nonempty (Iso l l), a subsingleton because the apex is
representable, so the actual output of Pg.coneEssSurj is the identity iso. -/
theorem S2125PresentationStrongFieldAtLift_eq_refl
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg.toWeak).square1.Cone W) :
    Pg.coneEssSurj W (S2118Conv f g T ptA Pg.toWeak s)
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))
        ⟨Pg.toWeak.isPullback.liftToX W (S2118Conv f g T ptA Pg.toWeak s)⟩
        ⟨Pg.toWeak.isPullback.liftToY W (S2118Conv f g T ptA Pg.toWeak s)⟩ =
      ⟨Iso.refl (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))⟩ := by
  haveI hthin : Subsingleton
      ((Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s)) ⟶
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))) :=
    S1827SubsingletonModRep _ _
  haveI hiso : Subsingleton
      (Iso (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))) :=
    ⟨fun a b => Iso.ext (Subsingleton.elim _ _)⟩
  exact Subsingleton.elim _ _

/-- The strong field's output does not depend on the comparison isomorphisms fed
to it: any two admissible inputs produce the same (trivial) conclusion. -/
theorem S2125PresentationStrongFieldAtLift_indep
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg.toWeak).square1.Cone W)
    (α : Iso (Pseudofunctor.StrongTrans.vcomp
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))
        (S2118PresentationSquare f g T ptA Pg.toWeak).toX)
      (S2118Conv f g T ptA Pg.toWeak s).toX)
    (β : Iso (Pseudofunctor.StrongTrans.vcomp
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))
        (S2118PresentationSquare f g T ptA Pg.toWeak).toY)
      (S2118Conv f g T ptA Pg.toWeak s).toY)
    (α' : Iso (Pseudofunctor.StrongTrans.vcomp
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))
        (S2118PresentationSquare f g T ptA Pg.toWeak).toX)
      (S2118Conv f g T ptA Pg.toWeak s).toX)
    (β' : Iso (Pseudofunctor.StrongTrans.vcomp
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))
        (S2118PresentationSquare f g T ptA Pg.toWeak).toY)
      (S2118Conv f g T ptA Pg.toWeak s).toY) :
    Pg.coneEssSurj W (S2118Conv f g T ptA Pg.toWeak s)
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))
        ⟨α⟩ ⟨β⟩ =
      Pg.coneEssSurj W (S2118Conv f g T ptA Pg.toWeak s)
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))
        ⟨α'⟩ ⟨β'⟩ := by
  haveI hthin : Subsingleton
      ((Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s)) ⟶
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))) :=
    S1827SubsingletonModRep _ _
  haveI hiso : Subsingleton
      (Nonempty (Iso (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s))
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s)))) :=
    ⟨fun a b => Subsingleton.elim _ _⟩
  exact Subsingleton.elim _ _

/-! ## 5. Consequences and consumers -/

/-- The unrestricted S2118 presentation twist gives the concrete API. -/
theorem S2125PresentationConcreteTwist_of_S2118
    (h : S2118PresentationTwist) : S2125PresentationConcreteTwist :=
  S2125PresentationConcreteTwist_iff_strongTwist.mpr
    (S2120StrongPresentationTwist_of_S2118 h)

/-- S2120's first missing gives the concrete API. -/
theorem S2125PresentationConcreteTwist_of_firstMissing
    (h : S2120FirstMissing) : S2125PresentationConcreteTwist :=
  S2125PresentationConcreteTwist_iff_coherent.mpr
    (S2123PresentationLiftCoherent_of_firstMissing h)

/-- S2123's cone-category API (the existence form plus 2-cell fullness at the
recorded lift) gives the concrete API. -/
theorem S2125PresentationConcreteTwist_of_coneCategoryAPI
    (h : S2123PresentationConeCategoryAPI) : S2125PresentationConcreteTwist :=
  S2125PresentationConcreteTwist_iff_coherent.mpr
    (S2123PresentationTwist_iff_liftConeMorCoherent.mpr
      (S2123StrongPresentationTwist_of_coneCategoryAPI h))

/-- The strong twist gives the concrete API. -/
theorem S2125PresentationConcreteTwist_of_strongTwist
    (h : S2120StrongPresentationTwist) : S2125PresentationConcreteTwist :=
  S2125PresentationConcreteTwist_iff_strongTwist.mpr h

/-- **Consumer form at S2110's strong input.**  The concrete API gives the twist
at the strong presentation selected by S2110StrongTwoFullData. -/
theorem S2125StrongPresentationTwist_for_strongTwoFullData
    (h : S2125PresentationConcreteTwist) (D : S2110StrongTwoFullData)
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
  S2125PresentationConcreteTwist_iff_strongTwist.mp h
    A B C f g T ptA (D.strongPresentation A B C f g T ptA) W s

/-! ## 6. Checks and axiom audit -/

#check @S2125TwistAt
#check @S2125DisplayedTwistAt
#check @S2125ConcreteTwistAt
#check @S2125ImageCone_commutes_app
#check @S2125TwistAt_iff_displayed
#check @S2125DisplayedTwistAt_iff_concrete
#check @S2125TwistAt_iff_concrete
#check @S2125LiftToXCompatible_recorded_iff
#check @S2125StrongFieldOfLift
#check @S2125EssSurjOf_iff_strongFieldOfLift
#check @S2125StrongFieldOfLift_congr
#check @S2125PresentationConeEssSurj_iff_strongFieldOfLift
#check S2125PresentationConcreteTwist
#check S2125PresentationConcreteTwistAt_iff_explicit
#check S2125PresentationConcreteTwist_iff_coherent
#check S2125PresentationConcreteTwist_iff_strongTwist
#check S2125PresentationRecordedComparison_iff
#check S2125PresentationRequiredTwoCellAPI
#check S2125PresentationRequiredTwoCellAPI_iff_liftConeMor
#check S2125PresentationRequiredTwoCellAPI_of_coherent
#check S2125PresentationConcreteTwist_of_requiredAndFull
#check S2125ExactFirstMissing
#check S2125SufficientAPI
#check S2125PresentationStrongFieldAtLift_eq_refl
#check S2125PresentationStrongFieldAtLift_indep
#check S2125PresentationConcreteTwist_of_S2118
#check S2125PresentationConcreteTwist_of_firstMissing
#check S2125PresentationConcreteTwist_of_coneCategoryAPI
#check S2125PresentationConcreteTwist_of_strongTwist
#check S2125StrongPresentationTwist_for_strongTwoFullData

#print axioms S2125ImageCone_commutes_app
#print axioms S2125TwistAt_iff_displayed
#print axioms S2125DisplayedTwistAt_iff_concrete
#print axioms S2125TwistAt_iff_concrete
#print axioms S2125LiftToXCompatible_recorded_iff
#print axioms S2125EssSurjOf_iff_strongFieldOfLift
#print axioms S2125StrongFieldOfLift_congr
#print axioms S2125PresentationConeEssSurj_iff_strongFieldOfLift
#print axioms S2125PresentationConcreteTwistAt_iff_explicit
#print axioms S2125PresentationConcreteTwist_iff_coherent
#print axioms S2125PresentationConcreteTwist_iff_strongTwist
#print axioms S2125PresentationRecordedComparison_iff
#print axioms S2125PresentationRequiredTwoCellAPI_iff_liftConeMor
#print axioms S2125PresentationRequiredTwoCellAPI_of_coherent
#print axioms S2125PresentationConcreteTwist_of_requiredAndFull
#print axioms S2125ExactFirstMissing
#print axioms S2125SufficientAPI
#print axioms S2125PresentationStrongFieldAtLift_eq_refl
#print axioms S2125PresentationStrongFieldAtLift_indep
#print axioms S2125PresentationConcreteTwist_of_S2118
#print axioms S2125PresentationConcreteTwist_of_firstMissing
#print axioms S2125PresentationConcreteTwist_of_coneCategoryAPI
#print axioms S2125PresentationConcreteTwist_of_strongTwist
#print axioms S2125StrongPresentationTwist_for_strongTwoFullData

end LeanFormal.IUT.XiFPaper.S2125PresentationCoherentActual