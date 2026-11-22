/-
# S1784: the missing unit 2-cell  toSource ≫ lift ≅ 𝟙  of the identity-point base change

## What this file is for

S1756 isolated the missing statement for "the source stack of a finite etale cover is
representable by its affine base-change model" as

  S1756FirstMissing : ∀ A, S1756End A = 𝟙 (S1733Model A),

where S1756End A = eval (toSource ≫ lift) is the self-endomorphism of the affine model
S_A = S1733Model A induced by the identity-point two-pullback.  S1756 proved that this is
equivalent to the existence of the unit 2-cell (S1756Unit_iff_end) and to S1743's
S1743SourceRetraction, that it holds whenever the structure morphism S_A ⟶ Spec R' is a
monomorphism, and that the recorded TwoPullbackWitness fields supply no such 2-cell.

This file attacks the statement itself.  Results, in order of strength:

* S1784EndTrans_fixes_lift: **unconditional**.  The endomorphism fixes the whole image of
  the lift: lift ≫ (toSource ≫ lift) ≅ lift.  Scheme-theoretically
  (S1784YonedaEval_lift_fixed), every point of the affine model that comes from the
  source stack is a fixed point of S1756End.

* S1784End_eq_one_of_point_from_lift: **unconditional**, and an equivalent but
  cancellation-free reformulation of S1756's retraction criterion.  If the identity point
  𝟙 (S_A) of the model is 2-isomorphic to *any* point coming from the source
  (∃ x, x ≫ lift ≅ 𝟙), then S1756End A = 𝟙.  S1756's S1756End_eq_one_of_retraction
  (toSource has a one-sided inverse) is the case x = toSource; the proof here never forms
  the bicategorical cancellation of S1756_unit_iso.

* S1784FirstMissing_iff_idPoint_from_lift: the missing statement is *equivalent* to
  "for every cover the identity point of its affine model comes from the source".  This is
  a purely geometric reformulation of the gap which never mentions the
  self-endomorphism: the obstruction is a point of S_A invisible to A.source.

* S1784LiftEssSurj and S1784End_eq_one_of_liftEssSurj: the exact half of the bicategorical
  universal property that is missing from TwoPullbackWitness, and the proof that adding it
  closes the statement (S1784FirstMissing_of_liftEssSurj).

## The exact obstruction, and why the recorded axioms do not suffice

TwoPullbackWitness (Iut/Foundations/Orbicurve.lean) records, for a square P,

* lift : Cone W → (W ⟶ P),
* liftToX, liftToY: the two projection 2-isomorphisms of that lift,
* liftTwoCell: the induced 2-cell between lifts, with its two projection formulas,
* twoCell_ext: two parallel 2-cells with equal whiskerings with toX and with toY are equal.

twoCell_ext is *faithfulness* of the comparison functor Hom(W,P) ⟶ Cone(W).  What is
missing is the converse direction, i.e. *essential surjectivity/fullness* of that
comparison: a 1-cell whose two projections agree with a cone must be 2-isomorphic to the
lift of that cone.  Write

  S1784LiftEssSurj A  :=  for every cone c with apex W and every f : W ⟶ P,
     f ≫ toX ≅ c.toX → f ≫ toY ≅ c.toY → Nonempty (f ≅ lift c).

With it the unit 2-cell is immediate: 𝟙 P and toSource ≫ lift have the same two
projections as the pullback's own cone (S1784EndTrans_toSource, S1784EndTrans_projection),
so both are 2-isomorphic to the lift of that cone, hence to each other
(S1784End_eq_one_of_liftEssSurj).

That the recorded axioms cannot supply this is not a guess: the recorded fields are satisfied,
with the conclusion failing, in the following model of the axiom system, in Cat, where the
square is degenerate.  Take X = Y = Z = 𝟙, toX, toY and point all constant, and let P be
the poset  0 < 1  regarded as a category (thin, so every hom-category of a functor
category into P is a subsingleton).

* every functor W ⟶ 𝟙 is unique, so Cone W is the terminal category;
* take lift W c := const 0, i.e. the constant functor to the object 0 of P: the two
  projection 2-isomorphisms exist because functors into 𝟙 are pairwise isomorphic;
* liftTwoCell is the identity 2-cell (lift is constant), and both projection formulas are
  subsingleton;
* twoCell_ext holds because P is thin.

Yet lift of the identity cone is const 0 : 𝟙 ⟶ P, so toSource ≫ lift is the constant
functor to 0 on P, which is not 2-isomorphic to 𝟙 P (it does not fix the object 1).
Consequently the unit 2-cell is *not* a consequence of the recorded fields; an honest
proof of S1756FirstMissing must use more of the geometry (the identity point of the square,
the finite etale map, or representability of the base) than the witness currently exports.
No fake 2-cell and no equivalence is introduced here: S1784LiftEssSurj is an honest,
identifiable hypothesis, and S1756SourceRepresentable is only ever derived from it.

## Axiom footprint

Only propext, Classical.choice and Quot.sound; see the #print axioms block at the end.
No sorry, no new axiom, no Shrink, ULift or PUnit.
-/

import tmp.sheaf.xif.paper.S1756CoverSourceRepresentabilityActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1784SourceRetractionUnitActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual

/-! ## 1. The self-transformation and its two projection equations -/

/-- The endomorphism 1-cell  toSource ≫ lift  of the model stack; its 2-Yoneda
evaluation is S1756End. -/
noncomputable def S1784EndTrans (A : S1728Cover) :
    Pseudofunctor.StrongTrans (S1743ModelStack A) (S1743ModelStack A) :=
  Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)

/-- The 2-Yoneda evaluation of the endomorphism 1-cell is S1756's S1756End. -/
theorem S1784EndTrans_eval (A : S1728Cover) :
    S1743YonedaEval (S1733Model A) (S1733Model A) (S1784EndTrans A) = S1756End A := rfl

/-- The comparison is a retraction with section the lift:  lift ≫ toSource ≅ 𝟙.
This is the unconditionally available triangle of the quasi-equivalence. -/
noncomputable def S1784Section (A : S1728Cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
      (Pseudofunctor.StrongTrans.id (S1743Source A)) :=
  (S1743BaseChange A).isPullback.liftToX (S1743Source A) (S1743IdentityCone A)

/-- The endomorphism has the same projection to the source as the identity. -/
theorem S1784EndTrans_toSource (A : S1728Cover) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1784EndTrans A) (S1756ToSource A))
      (S1756ToSource A)) := by
  refine ⟨?_⟩
  have h1 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
        (S1756ToSource A))
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))) :=
    S1756AssociatorIso _ _ _
  have h2 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A)))
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
        (Pseudofunctor.StrongTrans.id (S1743Source A))) :=
    S1756WhiskerLeftIso _ _ _ (S1784Section A)
  have h3 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
        (Pseudofunctor.StrongTrans.id (S1743Source A)))
      (S1756ToSource A) :=
    S1756RightUnitorIso (S1756ToSource A)
  exact h1.trans (h2.trans h3)

/-- The endomorphism has the same projection to the base as the identity: the 1-cell form
of S1756's S1756End_projection, extracted from its proof so that it can be fed to the
two-pullback universal property. -/
theorem S1784EndTrans_projection (A : S1728Cover) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1784EndTrans A) (S1756ProjectionMap A))
      (S1756ProjectionMap A)) := by
  refine ⟨?_⟩
  have h1 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
        (S1756ProjectionMap A))
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ProjectionMap A))) :=
    S1756AssociatorIso _ _ _
  have h2 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ProjectionMap A)))
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) A.map) :=
    S1756WhiskerLeftIso _ _ _ ((S1743BaseChange A).isPullback.liftToY
      (S1743Source A) (S1743IdentityCone A))
  have h3 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) A.map)
      (Pseudofunctor.StrongTrans.vcomp (S1756ProjectionMap A) S1733BasePoint) :=
    (S1743BaseChange A).commutes
  have h4 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1756ProjectionMap A) S1733BasePoint)
      (S1756ProjectionMap A) :=
    S1756RightUnitorIso (S1756ProjectionMap A)
  exact h1.trans (h2.trans (h3.trans h4))

/-! ## 2. The endomorphism fixes the image of the lift (unconditional) -/

/-- **Unconditional**: the self-endomorphism of the model fixes every point of the model
which comes from the source:  lift ≫ (toSource ≫ lift) ≅ lift.  This is the bicategorical
form of S1756End A ≫ projection = projection, for the source side instead of the base
side, and it is available without any new input. -/
theorem S1784EndTrans_fixes_lift (A : S1728Cover) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1784EndTrans A))
      (S1743Lift A)) := by
  refine ⟨?_⟩
  have h1 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
        (S1743Lift A))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id (S1743Source A)) (S1743Lift A)) :=
    S1756WhiskerRightIso _ _ (S1743Lift A) (S1784Section A)
  have h2 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
        (S1743Lift A)) :=
    (S1756AssociatorIso (S1743Lift A) (S1756ToSource A) (S1743Lift A)).symm
  have h3 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id (S1743Source A)) (S1743Lift A))
      (S1743Lift A) :=
    S1756LeftUnitorIso (S1743Lift A)
  exact h2.trans (h1.trans h3)

/-- **Unconditional, scheme level**: for every test scheme U and every U-point
x : h_U ⟶ A.source of the cover source, the induced point  eval (x ≫ lift) : U ⟶ S_A  of
the affine model is a fixed point of S1756End:

  eval (x ≫ lift) ≫ S1756End = eval (x ≫ lift).

Thus a counterexample to the missing statement can only come from a point of the model
which is not in the image of the source. -/
theorem S1784YonedaEval_lift_fixed (A : S1728Cover)
    (U : SchemeOverField S1726K)
    (x : Pseudofunctor.StrongTrans (S1743Y U) (S1743Source A)) :
    S1743YonedaEval U (S1733Model A)
        (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A)) ≫ S1756End A
      = S1743YonedaEval U (S1733Model A)
        (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A)) := by
  have h1 : Iso
      (Pseudofunctor.StrongTrans.vcomp x
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1784EndTrans A)))
      (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A)) :=
    S1756WhiskerLeftIso x _ _ (S1784EndTrans_fixes_lift A).some
  have h2 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A)) (S1784EndTrans A))
      (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A)) :=
    (S1756AssociatorIso x (S1743Lift A) (S1784EndTrans A)).trans h1
  have heq := S1743YonedaEval_congr_iso U (S1733Model A) h2
  rw [S1743YonedaEval_vcomp, S1784EndTrans_eval] at heq
  exact heq

/-! ## 3. A point of the model coming from the source forces the identity -/

/-- **Unconditional**: if the identity point of the affine model is 2-isomorphic to some
point coming from the source, then the self-endomorphism is the identity.

S1756's S1756End_eq_one_of_retraction (toSource has a one-sided inverse) is the special
case x = toSource of this hypothesis, and both are equivalent to the unit 2-cell; the point
form is the one the geometry of the identity point can supply, and this proof needs no
bicategorical cancellation lemma. -/
theorem S1784End_eq_one_of_point_from_lift (A : S1728Cover)
    (h : ∃ x : Pseudofunctor.StrongTrans (S1743ModelStack A) (S1743Source A),
      Nonempty (Iso
        (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A))
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A)))) :
    S1756End A = 𝟙 (S1733Model A) := by
  obtain ⟨x, ⟨e⟩⟩ := h
  have hunit : S1756Unit A := by
    refine ⟨?_⟩
    have h1 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A)) (S1784EndTrans A))
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) (S1784EndTrans A)) :=
      S1756WhiskerRightIso _ _ (S1784EndTrans A) e
    have h2 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A)) (S1784EndTrans A))
        (Pseudofunctor.StrongTrans.vcomp x
          (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1784EndTrans A))) :=
      S1756AssociatorIso x (S1743Lift A) (S1784EndTrans A)
    have h3 : Iso
        (Pseudofunctor.StrongTrans.vcomp x
          (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1784EndTrans A)))
        (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A)) :=
      S1756WhiskerLeftIso x _ _ (S1784EndTrans_fixes_lift A).some
    have h4 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) (S1784EndTrans A))
        (S1784EndTrans A) :=
      S1756LeftUnitorIso (S1784EndTrans A)
    exact h4.symm.trans ((h1.symm.trans (h2.trans h3)).trans e)
  exact (S1756Unit_iff_end A).mp hunit

/-- "Every point of the affine model comes from the source": the lift is surjective on
test-scheme points.  This is the precise point-level content of representability of the
cover source by its affine model. -/
def S1784LiftPointSurj (A : S1728Cover) : Prop :=
  ∀ (U : SchemeOverField S1726K)
    (y : Pseudofunctor.StrongTrans (S1743Y U) (S1743ModelStack A)),
    ∃ x : Pseudofunctor.StrongTrans (S1743Y U) (S1743Source A),
      Nonempty (Iso y (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A)))

/-- If the unit 2-cell exists then the lift is surjective on points: compose the inverse
of the unit with the projection to the source. -/
theorem S1784LiftPointSurj_of_unit (A : S1728Cover) (h : S1756Unit A) :
    S1784LiftPointSurj A := by
  obtain ⟨e⟩ := h
  intro U y
  refine ⟨Pseudofunctor.StrongTrans.vcomp y (S1756ToSource A), ⟨?_⟩⟩
  have h1 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp y (S1756ToSource A)) (S1743Lift A))
      (Pseudofunctor.StrongTrans.vcomp y
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))) :=
    S1756AssociatorIso y (S1756ToSource A) (S1743Lift A)
  have h2 : Iso
      (Pseudofunctor.StrongTrans.vcomp y
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)))
      (Pseudofunctor.StrongTrans.vcomp y
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) :=
    S1756WhiskerLeftIso y _ _ e
  have h3 : Iso
      (Pseudofunctor.StrongTrans.vcomp y
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) y :=
    S1756RightUnitorIso y
  exact (h1.trans (h2.trans h3)).symm

/-- Conversely, surjectivity of the lift on points gives the identity self-endomorphism (it
is enough to know it at the identity point, and this is exactly
S1784End_eq_one_of_point_from_lift). -/
theorem S1784End_eq_one_of_liftPointSurj (A : S1728Cover)
    (h : S1784LiftPointSurj A) :
    S1756End A = 𝟙 (S1733Model A) := by
  obtain ⟨x, ⟨e⟩⟩ :=
    h (S1733Model A) (Pseudofunctor.StrongTrans.id (S1743ModelStack A))
  exact S1784End_eq_one_of_point_from_lift A ⟨x, ⟨e.symm⟩⟩

/-- **The missing statement, in point form**: representability of the cover source by its
affine model holds if and only if every point of the model comes from the source.  So the
only possible obstruction is a point of S_A that is invisible to A.source; there is no
further hidden structure in the self-endomorphism. -/
theorem S1784FirstMissing_iff_liftPointSurj :
    S1756FirstMissing ↔ ∀ A : S1728Cover, S1784LiftPointSurj A := by
  constructor
  · intro h A
    exact S1784LiftPointSurj_of_unit A ((S1756Unit_iff_end A).mpr (h A))
  · intro h A
    exact S1784End_eq_one_of_liftPointSurj A (h A)

/-- **Geometric reformulation of the missing statement**: the self-endomorphism of every
affine model is the identity if and only if, for every cover, the identity point of the
model comes from the source.  This version never mentions the endomorphism, only the image
of the source inside the model. -/
theorem S1784FirstMissing_iff_idPoint_from_lift :
    S1756FirstMissing ↔
      ∀ A : S1728Cover,
        ∃ x : Pseudofunctor.StrongTrans (S1743ModelStack A) (S1743Source A),
          Nonempty (Iso
            (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A))
            (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) := by
  constructor
  · intro h A
    exact ⟨S1756ToSource A, (S1756Unit_iff_end A).mpr (h A)⟩
  · intro h A
    exact S1784End_eq_one_of_point_from_lift A (h A)

/-- S1743's retraction criterion and the point criterion are equivalent: both
characterise the unit 2-cell.  S1756's formulation is the case x = toSource of the point
criterion, while the point criterion is what the geometry of the identity point actually
provides, and its proof needs no bicategorical cancellation lemma. -/
theorem S1784Retraction_iff_point_from_lift :
    S1743SourceRetraction ↔
      ∀ A : S1728Cover,
        ∃ x : Pseudofunctor.StrongTrans (S1743ModelStack A) (S1743Source A),
          Nonempty (Iso
            (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A))
            (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) := by
  rw [S1756Retraction_iff_firstMissing, S1784FirstMissing_iff_idPoint_from_lift]

/-! ## 4. The missing half of the two-pullback universal property -/

/-- The cone over the identity-point base-change square given by the pullback's own two
projections.  Its lift is the candidate "counit" S_A ⟶ S_A supplied by the universal
property. -/
noncomputable def S1784PullbackCone (A : S1728Cover) :
    (S1743Square A).Cone (S1743ModelStack A) where
  toX := S1756ToSource A
  toY := S1756ProjectionMap A
  commutes := (S1743BaseChange A).commutes

/-- The lift of the pullback's own cone. -/
noncomputable def S1784Counit (A : S1728Cover) :
    Pseudofunctor.StrongTrans (S1743ModelStack A) (S1743ModelStack A) :=
  (S1743BaseChange A).isPullback.lift (S1743ModelStack A) (S1784PullbackCone A)

/-- The two pieces of the universal property which the recorded TwoPullbackWitness does
*not* export, in the exact form in which the argument below needs them: the lift of the
pullback's own cone is 2-isomorphic to the identity, and to toSource ≫ lift.

Both are instances of the missing essential surjectivity of the comparison
Hom(W,P) ⟶ Cone(W); see S1784LiftEssSurj. -/
def S1784CounitData (A : S1728Cover) : Prop :=
  Nonempty (Iso (S1784Counit A) (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) ∧
    Nonempty (Iso (S1784Counit A) (S1784EndTrans A))

/-- The minimal additional input gives the unit 2-cell, hence the identity
self-endomorphism. -/
theorem S1784End_eq_one_of_counitData (A : S1728Cover) (h : S1784CounitData A) :
    S1756End A = 𝟙 (S1733Model A) := by
  obtain ⟨h1, h2⟩ := h
  exact (S1756Unit_iff_end A).mp ⟨h2.some.symm.trans h1.some⟩

/-- The missing half of the two-pullback universal property: a 1-cell out of a cone's apex
whose projections are 2-isomorphic to the cone's projections is 2-isomorphic to the lift.
TwoPullbackWitness proves the opposite direction (twoCell_ext, faithfulness); this is
essential surjectivity of the comparison with the cone category, i.e. the statement that a
map into the pullback is determined by its two projections. -/
def S1784LiftEssSurj (A : S1728Cover) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K) (c : (S1743Square A).Cone W)
    (f : Pseudofunctor.StrongTrans W (S1743ModelStack A)),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f (S1743Square A).toX) c.toX) →
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f (S1743Square A).toY) c.toY) →
        Nonempty (Iso f ((S1743BaseChange A).isPullback.lift W c))

/-- **Main structural theorem**: the missing half of the universal property closes
S1756FirstMissing for the cover.  Both 𝟙 P and toSource ≫ lift have the same two
projections as the pullback's own cone, so both are 2-isomorphic to its lift. -/
theorem S1784End_eq_one_of_liftEssSurj (A : S1728Cover) (h : S1784LiftEssSurj A) :
    S1756End A = 𝟙 (S1733Model A) := by
  obtain ⟨eleft⟩ :=
    h (S1743ModelStack A) (S1784PullbackCone A) (S1784EndTrans A)
      (S1784EndTrans_toSource A) (S1784EndTrans_projection A)
  obtain ⟨eid⟩ :=
    h (S1743ModelStack A) (S1784PullbackCone A)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A))
      ⟨S1756LeftUnitorIso (S1756ToSource A)⟩
      ⟨S1756LeftUnitorIso (S1756ProjectionMap A)⟩
  exact S1784End_eq_one_of_counitData A ⟨⟨eid.symm⟩, ⟨eleft.symm⟩⟩

/-- The missing half of the universal property gives the unit 2-cell for every cover,
hence S1743's missing retraction statement. -/
theorem S1784Retraction_of_liftEssSurj (h : ∀ A : S1728Cover, S1784LiftEssSurj A) :
    S1743SourceRetraction :=
  fun A => ⟨S1743Lift A, (S1756Unit_iff_end A).mpr (S1784End_eq_one_of_liftEssSurj A (h A))⟩

/-- **The statement of the task, from the missing half of the universal property.** -/
theorem S1784FirstMissing_of_liftEssSurj (h : ∀ A : S1728Cover, S1784LiftEssSurj A) :
    S1756FirstMissing :=
  fun A => S1784End_eq_one_of_liftEssSurj A (h A)

/-- Representability of every cover source by its affine finite etale model, from the
missing half of the universal property. -/
theorem S1784SourceRepresentableAll_of_liftEssSurj
    (h : ∀ A : S1728Cover, S1784LiftEssSurj A) :
    S1756SourceRepresentableAll :=
  S1756SourceRepresentableAll_of_firstMissing (S1784FirstMissing_of_liftEssSurj h)

/-! ## 5. What is *not* proved here

S1784LiftEssSurj is not constructed for any cover, not even in the single-cone form of
S1784CounitData, and S1756FirstMissing is not inhabited.  Concretely:

* S1784EndTrans_projection and S1784EndTrans_toSource produce two 2-isomorphisms from
  toSource ≫ lift to the projections of the pullback cone; twoCell_ext cannot turn them
  into a 2-cell  toSource ≫ lift ⟶ 𝟙, because it only compares 2-cells with a common
  source and target.
* The three points where a proof would have to use the geometry rather than the witness
  are: the identity point of the square (point = 𝟙), representability of the base
  h_{Spec R'}, and finite etaleness of projection.  None of the recorded fields
  distinguishes the identity point from an arbitrary point, and the degenerate Cat model
  in the header shows that the recorded fields are consistent with a failing unit.
* S1756's monomorphism special case (S1756End_eq_one_of_mono) remains the only
  scheme-level sufficient condition; the criteria added here are point-level, and none of
  the sufficient conditions is known to hold for a single cover.  Conversely the
  monomorphism hypothesis is not implied by the point criteria, so all three are
  independent records of the same gap.
-/

/-! ## 6. Checks -/

#check S1784EndTrans
#check S1784EndTrans_eval
#check S1784Section
#check S1784EndTrans_toSource
#check S1784EndTrans_projection
#check S1784EndTrans_fixes_lift
#check S1784YonedaEval_lift_fixed
#check S1784End_eq_one_of_point_from_lift
#check S1784Retraction_iff_point_from_lift
#check S1784FirstMissing_iff_idPoint_from_lift
#check S1784LiftPointSurj
#check S1784LiftPointSurj_of_unit
#check S1784End_eq_one_of_liftPointSurj
#check S1784FirstMissing_iff_liftPointSurj
#check S1784PullbackCone
#check S1784Counit
#check S1784CounitData
#check S1784End_eq_one_of_counitData
#check S1784LiftEssSurj
#check S1784End_eq_one_of_liftEssSurj
#check S1784Retraction_of_liftEssSurj
#check S1784FirstMissing_of_liftEssSurj
#check S1784SourceRepresentableAll_of_liftEssSurj

#print axioms S1784EndTrans
#print axioms S1784EndTrans_eval
#print axioms S1784Section
#print axioms S1784EndTrans_toSource
#print axioms S1784EndTrans_projection
#print axioms S1784EndTrans_fixes_lift
#print axioms S1784YonedaEval_lift_fixed
#print axioms S1784End_eq_one_of_point_from_lift
#print axioms S1784Retraction_iff_point_from_lift
#print axioms S1784FirstMissing_iff_idPoint_from_lift
#print axioms S1784LiftPointSurj_of_unit
#print axioms S1784End_eq_one_of_liftPointSurj
#print axioms S1784FirstMissing_iff_liftPointSurj
#print axioms S1784PullbackCone
#print axioms S1784Counit
#print axioms S1784End_eq_one_of_counitData
#print axioms S1784End_eq_one_of_liftEssSurj
#print axioms S1784Retraction_of_liftEssSurj
#print axioms S1784FirstMissing_of_liftEssSurj
#print axioms S1784SourceRepresentableAll_of_liftEssSurj

end LeanFormal.IUT.XiFPaper.S1784SourceRetractionUnitActual
