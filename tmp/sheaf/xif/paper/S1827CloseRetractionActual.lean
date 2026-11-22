/-
# S1827: the canonical comparison of the recorded identity-point square with the actual
2-pullback, the exact characterisation of the missing coherence, and the closure of the
retraction targets

## What is proved here

S1804 constructed the actual 2-pullback of the cospan `(A.map, id)` of the identity-point
base-change square: its apex is the cover source `X = A.source` itself, with projections
`id_X` and `A.map`, and its 1-cell uniqueness is `S1804Source_isPullback`.  The recorded
square

    P = Y(S_A) --toSource--> X = A.source
       |                        |
     toY                       A.map
       v                        v
    Y = Y(Spec R') --id--> Z = Y(Spec R')

has apex `P = S1743ModelStack A` and is only known to satisfy the recorded
`TwoPullbackWitness` fields (lift, the two projection 2-cells, the action on cone
morphisms and 2-cell extensionality).

This file performs the comparison of the recorded square with the actual 2-pullback and
decides exactly what is missing.

* `S1827Comparison` is the canonical comparison 1-cell `P ⟶ X`.  By the actual
  pullback's 1-cell uniqueness (`S1827SquareMap_apex_unique`) it is *the* comparison of
  the recorded square with the actual pullback: every 1-cell `m'` whose two projections
  agree with the recorded legs is 2-isomorphic to `toSource`.  Hence the comparison is
  `toSource` itself and nothing else can play its role.

* `S1827Comparison_toX`, `S1827Comparison_toY` are the two 2-cells exhibiting the
  comparison as a map of squares over the common cospan; they are not new data but the
  right unitor and the recorded `commutes` cell.

* `S1827ComparisonQuasiEquiv A` is the honest 2-categorical statement "the comparison is
  an equivalence": an inverse 1-cell with the two triangular 2-isomorphisms.

* **Exact characterisation** (`S1827MissingCharacterisation`).  All of the following are
  equivalent, for every cover:

    - `S1827ConeEssSurj A`: the *essential-surjectivity half of the cone comparison*
      `Hom(W,P) ⟶ Cone(W)`, i.e. the missing half of the 2-dimensional universal
      property of the recorded square;
    - the canonical comparison `P ⟶ X` is a quasi-equivalence;
    - the unit 2-cell `toSource ≫ lift ≅ 𝟙` exists (`S1756Unit A`);
    - the self-endomorphism `S1756End A` of the affine model is the identity;
    - `S1784LiftEssSurj A` / `S1804RecordedActual A`.

  The direction "cone essential surjectivity ⟹ comparison is an equivalence" is the
  2-categorical limit-uniqueness argument: the recorded square and the actual pullback
  have the same cospan and the recorded legs, the unique comparison is `toSource`, its
  inverse must be the recorded lift `S1743Lift` (proved: any quasi-inverse is
  2-isomorphic to the lift, `S1827Comparison_inverse_unique`), and the only missing
  datum is the unit 2-cell, which the cone comparison supplies at the square's own cone.
  The converse direction uses right cancellation along `toSource` (S1804).

* **Closure** (`S1827FirstMissing_closure`): the single missing coherence implies
  `S1804FirstMissing`, `S1756FirstMissing`, `S1758FirstMissing`,
  `S1743SourceRetraction` and `S1756SourceRepresentableAll`.

* **An unconditional instance** (`S1827ComparisonQuasiEquiv_of_mono`): whenever the
  structure morphism `S_A ⟶ Spec R'` is a monomorphism the comparison *is* an
  equivalence and all the targets follow (S1756's monomorphism criterion transported to
  the comparison).  So the reduction is not vacuous.

* **No extra coherence on given 2-cells** (`S1827Unit_hom_unique`): the apex
  `P = Y(S_A)` is a representable stack, whose fibers are discrete categories;
  consequently all parallel 2-cells between 1-cells of the model are equal, so a unit
  2-cell is unique when it exists.  The gap is a question of *existence*, not of the
  coherence of a chosen 2-cell.

## The honest boundary: the first missing statement

`S1827FirstMissing : Prop := ∀ A, S1827ConeEssSurj A` is *not proved*, and it is not a
consequence of the recorded `TwoPullbackWitness` fields: S1801 formalised a square with a
recorded witness whose cone comparison fails to be essentially surjective
(`S1801NoGenericEssSurj`), and the failure there is precisely the non-existence of a
2-cell (`S1801DegenerateNotIso`), not the incoherence of a given one.  Section 7 records
the same refutation for the ess-surjectivity shape used here.

Hence the exact first missing statement is

  for every cover `A`, the cone comparison `Hom(W, S_A) ⟶ Cone(W)` of the recorded
  identity-point square is essentially surjective on 1-cells (equivalently: the recorded
  `TwoPullbackWitness` must be upgraded to the full 2-dimensional universal property, or
  the comparison `toSource` must be proved to be an equivalence by geometric input).

Limitation of the refutation, stated exactly: S1801's model has a *constant* apex,
whereas the apex of a cover's identity-point square is the representable stack
`Y(S_A)`.  So the refutation shows that the recorded fields do not imply the missing
coherence *as a matter of 2-categorical algebra*; it is not a counterexample inside the
cover situation, and the question whether the geometric input of the actual base change
forces the missing coherence is left open here.  What is settled is that no proof can
proceed from the recorded witness alone.

The natural repair, therefore, is a *definition* change: replace
`TwoPullbackWitness` in `EtaleStackBaseChangePresentation.isPullback` by the full
2-categorical universal property of the square (the cone comparison is an equivalence of
categories).  By `S1827MissingCharacterisation` this single change, and no further
coherence condition, closes `S1804FirstMissing`, `S1756FirstMissing`,
`S1758FirstMissing` and `S1743SourceRetraction`.  Changing the recorded structure is
not done here, since the recorded definitions are part of the target.

No fake 2-cell, no fake equivalence and no new axiom are introduced; the missing unit
2-cell is never assumed silently: it is a named hypothesis whose exact strength is proved
above.

## Axiom footprint

Only `propext`, `Classical.choice` and `Quot.sound`; see the `#print axioms` block.
-/

import tmp.sheaf.xif.paper.S1804IsoCommaPullbackActual
import tmp.sheaf.xif.paper.S1801LiftEssSurjActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual

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
open LeanFormal.IUT.XiFPaper.S1758SourceRetractionActual
open LeanFormal.IUT.XiFPaper.S1784SourceRetractionUnitActual
open LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual
open LeanFormal.IUT.XiFPaper.S1804IsoCommaPullbackActual

/-! ## 1. The comparison of the recorded square with the actual 2-pullback -/

/-- The recorded square, read as a cone over the actual pullback square: both squares have
the same cospan `(A.map, id)`, so the two legs of the recorded square are exactly a cone
over the actual square with apex `P = S1743ModelStack A`. -/
noncomputable def S1827RecordedCone (A : S1728Cover) :
    (S1804SourceSquare A).Cone (S1743ModelStack A) where
  toX := (S1743Square A).toX
  toY := (S1743Square A).toY
  commutes := (S1743Square A).commutes

/-- The canonical comparison 1-cell from the recorded apex to the actual 2-pullback: the
lift of the recorded square's own cone along the actual pullback. -/
noncomputable def S1827Comparison (A : S1728Cover) :
    Pseudofunctor.StrongTrans (S1743ModelStack A) (S1743Source A) :=
  S1804SourceLift A (S1827RecordedCone A)

/-- The comparison is the recorded comparison 1-cell `toSource`: the lift of a cone along
the actual pullback (whose source projection is the identity) is the cone's leg to the
source. -/
theorem S1827Comparison_def (A : S1728Cover) :
    S1827Comparison A = S1756ToSource A := rfl

/-- First comparison 2-cell: the comparison followed by the actual source projection is
the recorded source leg. -/
noncomputable def S1827Comparison_toX (A : S1728Cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1827Comparison A)
        (S1804SourceSquare A).toX) (S1743Square A).toX :=
  S1756RightUnitorIso (S1756ToSource A)

/-- Second comparison 2-cell: the comparison followed by the actual base projection is
the recorded base leg, by the recorded commuting cell. -/
noncomputable def S1827Comparison_toY (A : S1728Cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1827Comparison A)
        (S1804SourceSquare A).toY) (S1743Square A).toY :=
  (S1743BaseChange A).commutes.trans (S1756RightUnitorIso (S1756ProjectionMap A))

/-- A 1-cell from the recorded apex to the actual pullback together with the two 2-cells
that make it a map of squares over the common cospan. -/
structure S1827SquareMap (A : S1728Cover) where
  /-- The 1-cell of the comparison. -/
  apex : Pseudofunctor.StrongTrans (S1743ModelStack A) (S1743Source A)
  /-- Agreement with the recorded source leg. -/
  toX : Iso (Pseudofunctor.StrongTrans.vcomp apex (S1804SourceSquare A).toX)
    (S1743Square A).toX
  /-- Agreement with the recorded base leg. -/
  toY : Iso (Pseudofunctor.StrongTrans.vcomp apex (S1804SourceSquare A).toY)
    (S1743Square A).toY

/-- The canonical comparison as a map of squares. -/
noncomputable def S1827ComparisonMap (A : S1728Cover) : S1827SquareMap A where
  apex := S1827Comparison A
  toX := S1827Comparison_toX A
  toY := S1827Comparison_toY A

/-- **2-categorical limit uniqueness, uniqueness of the comparison.**  Every 1-cell whose
two projections agree with the recorded legs is 2-isomorphic to the canonical comparison:
the actual pullback's 1-cell uniqueness pins the comparison down to `toSource`. -/
theorem S1827SquareMap_apex_unique (A : S1728Cover) (m : S1827SquareMap A) :
    Nonempty (Iso m.apex (S1827Comparison A)) :=
  S1804Source_isPullback A (S1827RecordedCone A) m.apex ⟨m.toX⟩ ⟨m.toY⟩

/-- **Uniqueness of the inverse.**  Any 1-cell inverting the comparison is 2-isomorphic to
the recorded lift `S1743Lift`: the inverse side of the comparison is not new data. -/
theorem S1827Comparison_inverse_unique (A : S1728Cover)
    (inv : Pseudofunctor.StrongTrans (S1743Source A) (S1743ModelStack A))
    (u : Iso (Pseudofunctor.StrongTrans.vcomp (S1827Comparison A) inv)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) :
    Nonempty (Iso inv (S1743Lift A)) := by
  refine ⟨?_⟩
  have e1 : Iso inv
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id (S1743Source A)) inv) :=
    (S1756LeftUnitorIso inv).symm
  have e2 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id (S1743Source A)) inv)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1827Comparison A)) inv) :=
    (S1756WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1827Comparison A))
      (Pseudofunctor.StrongTrans.id (S1743Source A)) inv (S1784Section A)).symm
  have e3 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1827Comparison A)) inv)
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
        (Pseudofunctor.StrongTrans.vcomp (S1827Comparison A) inv)) :=
    S1756AssociatorIso (S1743Lift A) (S1827Comparison A) inv
  have e4 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
        (Pseudofunctor.StrongTrans.vcomp (S1827Comparison A) inv))
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) :=
    S1756WhiskerLeftIso (S1743Lift A) _ _ u
  have e5 : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) (S1743Lift A) :=
    S1756RightUnitorIso (S1743Lift A)
  exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

/-! ## 2. The comparison is an equivalence, exactly when the missing unit exists -/

/-- The honest 2-categorical form of "the canonical comparison is an equivalence": an
inverse 1-cell with the two triangular 2-isomorphisms. -/
def S1827ComparisonQuasiEquiv (A : S1728Cover) : Prop :=
  ∃ inv : Pseudofunctor.StrongTrans (S1743Source A) (S1743ModelStack A),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp (S1827Comparison A) inv)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) ∧
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp inv (S1827Comparison A))
      (Pseudofunctor.StrongTrans.id (S1743Source A)))

/-- The counit triangle of the comparison is available unconditionally: the recorded lift
is a right inverse of the comparison. -/
theorem S1827Comparison_counit (A : S1728Cover) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1827Comparison A))
      (Pseudofunctor.StrongTrans.id (S1743Source A))) :=
  ⟨S1784Section A⟩

/-- The unit 2-cell makes the comparison a quasi-equivalence, with the recorded lift as
inverse. -/
theorem S1827ComparisonQuasiEquiv_of_unit (A : S1728Cover) (h : S1756Unit A) :
    S1827ComparisonQuasiEquiv A :=
  ⟨S1743Lift A, h, S1827Comparison_counit A⟩

/-- Conversely, a quasi-equivalence of the comparison forces the missing unit 2-cell: the
inverse is forced to be the lift, and the unit 2-cell is the bicategorical cancellation
lemma of S1756 applied to the retraction. -/
theorem S1827Unit_of_comparisonQuasiEquiv (A : S1728Cover)
    (h : S1827ComparisonQuasiEquiv A) : S1756Unit A := by
  obtain ⟨inv, ⟨u, _⟩⟩ := h
  exact (S1756Unit_iff_end A).mpr (S1756End_eq_one_of_retraction A ⟨inv, u⟩)

/-- **The comparison is an equivalence exactly when the unit 2-cell exists.** -/
theorem S1827ComparisonQuasiEquiv_iff_unit (A : S1728Cover) :
    S1827ComparisonQuasiEquiv A ↔ S1756Unit A :=
  ⟨S1827Unit_of_comparisonQuasiEquiv A, S1827ComparisonQuasiEquiv_of_unit A⟩

/-- Equivalently, the comparison is an equivalence exactly when the self-endomorphism of
the affine model is the identity. -/
theorem S1827ComparisonQuasiEquiv_iff_end (A : S1728Cover) :
    S1827ComparisonQuasiEquiv A ↔ S1756End A = 𝟙 (S1733Model A) :=
  (S1827ComparisonQuasiEquiv_iff_unit A).trans (S1756Unit_iff_end A)

/-! ## 3. The exact missing coherence: essential surjectivity of the cone comparison -/

/-- The missing half of the 2-dimensional universal property of the recorded square: the
cone comparison `Hom(W, P) ⟶ Cone(W)` is essentially surjective, i.e. a 1-cell whose two
projections agree with a cone is 2-isomorphic to the lift of that cone.

The recorded `TwoPullbackWitness` supplies the opposite direction (`liftTwoCell`,
`twoCell_ext`).  This proposition is the exact extra input; it is *not* implied by the
recorded fields (S1801, re-exported in Section 7). -/
def S1827ConeEssSurj (A : S1728Cover) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K) (c : (S1743Square A).Cone W)
    (f : Pseudofunctor.StrongTrans W (S1743ModelStack A)),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f (S1743Square A).toX) c.toX) →
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f (S1743Square A).toY) c.toY) →
        Nonempty (Iso f ((S1743BaseChange A).isPullback.lift W c))

/-- The missing coherence is literally S1784's essential-surjectivity statement. -/
theorem S1827ConeEssSurj_iff_liftEssSurj (A : S1728Cover) :
    S1827ConeEssSurj A ↔ S1784LiftEssSurj A :=
  Iff.rfl

/-- **2-categorical limit uniqueness, forward direction.**  If the recorded square
satisfies the missing half of its 2-dimensional universal property, then the canonical
comparison to the actual 2-pullback is an equivalence.

The proof is the standard one: the recorded square's own cone is compared with the
identity, both have the projections of the square itself, so the cone comparison gives
2-cells from `𝟙_P` and from `toSource ≫ lift` to the same lift; hence the unit 2-cell. -/
theorem S1827ComparisonQuasiEquiv_of_coneEssSurj (A : S1728Cover)
    (h : S1827ConeEssSurj A) : S1827ComparisonQuasiEquiv A := by
  refine S1827ComparisonQuasiEquiv_of_unit A ?_
  have hc : S1784CounitData A := by
    constructor
    · obtain ⟨e⟩ := h (S1743ModelStack A) (S1784PullbackCone A)
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A))
        ⟨S1756LeftUnitorIso (S1756ToSource A)⟩
        ⟨S1756LeftUnitorIso (S1756ProjectionMap A)⟩
      exact ⟨e.symm⟩
    · obtain ⟨e⟩ := h (S1743ModelStack A) (S1784PullbackCone A) (S1784EndTrans A)
        (S1784EndTrans_toSource A) (S1784EndTrans_projection A)
      exact ⟨e.symm⟩
  exact (S1756Unit_iff_end A).mpr (S1784End_eq_one_of_counitData A hc)

/-- **2-categorical limit uniqueness, converse direction.**  If the comparison to the
actual 2-pullback is an equivalence, then the recorded square is a genuine 2-pullback on
1-cells: right cancellation along the comparison (S1804) turns agreement of projections
into the required 2-isomorphism. -/
theorem S1827ConeEssSurj_of_comparisonQuasiEquiv (A : S1728Cover)
    (h : S1827ComparisonQuasiEquiv A) : S1827ConeEssSurj A :=
  S1804LiftEssSurjOfUnit A (S1827Unit_of_comparisonQuasiEquiv A h)

/-- **The exact characterisation of the gap.**  The recorded square has the full
2-dimensional universal property on 1-cells if and only if its canonical comparison with
the actual 2-pullback is an equivalence. -/
theorem S1827ComparisonQuasiEquiv_iff_coneEssSurj (A : S1728Cover) :
    S1827ComparisonQuasiEquiv A ↔ S1827ConeEssSurj A :=
  ⟨S1827ConeEssSurj_of_comparisonQuasiEquiv A,
    S1827ComparisonQuasiEquiv_of_coneEssSurj A⟩

/-- The comparison is an equivalence exactly when S1804's recorded-actual statement
holds. -/
theorem S1827ComparisonQuasiEquiv_iff_recordedActual (A : S1728Cover) :
    S1827ComparisonQuasiEquiv A ↔ S1804RecordedActual A :=
  (S1827ComparisonQuasiEquiv_iff_unit A).trans (S1804RecordedActual_iff_unit A).symm

/-- All forms of the missing datum for one cover, in one statement. -/
theorem S1827MissingCharacterisation (A : S1728Cover) :
    (S1827ConeEssSurj A ↔ S1827ComparisonQuasiEquiv A) ∧
      (S1827ComparisonQuasiEquiv A ↔ S1756Unit A) ∧
      (S1756Unit A ↔ S1756End A = 𝟙 (S1733Model A)) ∧
      (S1827ComparisonQuasiEquiv A ↔ S1804RecordedActual A) :=
  ⟨(S1827ComparisonQuasiEquiv_iff_coneEssSurj A).symm,
    S1827ComparisonQuasiEquiv_iff_unit A,
    S1756Unit_iff_end A,
    S1827ComparisonQuasiEquiv_iff_recordedActual A⟩

/-! ## 4. The first missing statement and the closure of the targets -/

/-- **The exact first missing statement.**  For every cover, the recorded identity-point
square's cone comparison is essentially surjective on 1-cells (equivalently: the recorded
`TwoPullbackWitness` must be upgraded to the full 2-dimensional universal property of the
identity-point base change). -/
def S1827FirstMissing : Prop := ∀ A : S1728Cover, S1827ConeEssSurj A

/-- The first missing statement is exactly S1804's. -/
theorem S1827FirstMissing_iff_S1804 : S1827FirstMissing ↔ S1804FirstMissing :=
  Iff.rfl

/-- The first missing statement is exactly S1756's endomorphism equation. -/
theorem S1827FirstMissing_iff_S1756 : S1827FirstMissing ↔ S1756FirstMissing :=
  S1827FirstMissing_iff_S1804.trans S1804FirstMissing_iff_S1756

/-- The first missing statement is exactly S1743's retraction statement. -/
theorem S1827FirstMissing_iff_sourceRetraction :
    S1827FirstMissing ↔ S1743SourceRetraction :=
  S1827FirstMissing_iff_S1804.trans S1804FirstMissing_iff_sourceRetraction

/-- The first missing statement is exactly S1758's lift-cone-isomorphism statement. -/
theorem S1827FirstMissing_iff_S1758 : S1827FirstMissing ↔ S1758FirstMissing :=
  S1827FirstMissing_iff_S1804.trans S1804FirstMissing_iff_S1758

/-- The first missing statement is exactly the assertion that every canonical comparison
is an equivalence. -/
theorem S1827FirstMissing_iff_comparisonEquiv :
    S1827FirstMissing ↔ ∀ A : S1728Cover, S1827ComparisonQuasiEquiv A := by
  constructor
  · intro h A
    exact S1827ComparisonQuasiEquiv_of_coneEssSurj A (h A)
  · intro h A
    exact S1827ConeEssSurj_of_comparisonQuasiEquiv A (h A)

/-- Every canonical comparison is an equivalence once the missing coherence is supplied. -/
theorem S1827ComparisonQuasiEquiv_of_firstMissing (h : S1827FirstMissing) :
    ∀ A : S1728Cover, S1827ComparisonQuasiEquiv A :=
  S1827FirstMissing_iff_comparisonEquiv.mp h

/-- The missing coherence gives S1804's recorded-actual statement. -/
theorem S1827FirstMissing_to_S1804 (h : S1827FirstMissing) : S1804FirstMissing :=
  S1827FirstMissing_iff_S1804.mp h

/-- The missing coherence gives S1756's first missing statement. -/
theorem S1827FirstMissing_to_S1756 (h : S1827FirstMissing) : S1756FirstMissing :=
  S1827FirstMissing_iff_S1756.mp h

/-- The missing coherence gives S1743's source retraction. -/
theorem S1827FirstMissing_to_sourceRetraction (h : S1827FirstMissing) :
    S1743SourceRetraction :=
  S1827FirstMissing_iff_sourceRetraction.mp h

/-- The missing coherence gives S1758's first missing statement. -/
theorem S1827FirstMissing_to_S1758 (h : S1827FirstMissing) : S1758FirstMissing :=
  S1827FirstMissing_iff_S1758.mp h

/-- The missing coherence gives representability of every cover source by its affine
finite-etale model. -/
theorem S1827FirstMissing_to_sourceRepresentableAll (h : S1827FirstMissing) :
    S1756SourceRepresentableAll :=
  S1804FirstMissing_to_sourceRepresentableAll (S1827FirstMissing_iff_S1804.mp h)

/-- **Closure of the targets from the single missing coherence.** -/
theorem S1827FirstMissing_closure (h : S1827FirstMissing) :
    S1804FirstMissing ∧ S1756FirstMissing ∧ S1758FirstMissing ∧
      S1743SourceRetraction ∧ S1756SourceRepresentableAll :=
  ⟨S1827FirstMissing_to_S1804 h, S1827FirstMissing_to_S1756 h,
    S1827FirstMissing_to_S1758 h, S1827FirstMissing_to_sourceRetraction h,
    S1827FirstMissing_to_sourceRepresentableAll h⟩

/-! ## 4b. From the comparison to representability of the cover source -/

/-- A quasi-equivalence of the comparison is literally a stack quasi-equivalence between
the affine model and the cover source, with the comparison as forward 1-cell. -/
noncomputable def S1827StackEquivOfComparison (A : S1728Cover)
    (h : S1827ComparisonQuasiEquiv A) :
    S1756StackEquiv (S1743ModelStack A) (S1743Source A) where
  hom := S1827Comparison A
  inv := h.choose
  unit := h.choose_spec.1.some
  counit := h.choose_spec.2.some

/-- The comparison being an equivalence is exactly representability of the cover source
by its affine finite-etale model. -/
theorem S1827SourceRepresentable_of_comparisonQuasiEquiv (A : S1728Cover)
    (h : S1827ComparisonQuasiEquiv A) : S1756SourceRepresentable A :=
  ⟨S1827StackEquivOfComparison A h⟩

/-- The comparison being an equivalence for every cover gives representability of every
cover source. -/
theorem S1827SourceRepresentableAll_of_comparisonEquiv
    (h : ∀ A : S1728Cover, S1827ComparisonQuasiEquiv A) :
    S1756SourceRepresentableAll :=
  fun A => S1827SourceRepresentable_of_comparisonQuasiEquiv A (h A)

/-! ## 5. An unconditional instance: the monomorphism case -/

/-- **The comparison is an equivalence whenever the structure morphism of the affine
model is a monomorphism.**  This is S1756's monomorphism criterion transported to the
comparison; it exhibits a non-vacuous class of covers for which all the targets hold. -/
theorem S1827ComparisonQuasiEquiv_of_mono (A : S1728Cover)
    (hmono : Mono (S1756Projection A)) : S1827ComparisonQuasiEquiv A :=
  S1827ComparisonQuasiEquiv_of_unit A
    ((S1756Unit_iff_end A).mpr (S1756End_eq_one_of_mono A hmono))

/-- The same, uniformly in the cover. -/
theorem S1827ComparisonQuasiEquiv_of_monoAll
    (h : ∀ A : S1728Cover, Mono (S1756Projection A)) :
    ∀ A : S1728Cover, S1827ComparisonQuasiEquiv A :=
  fun A => S1827ComparisonQuasiEquiv_of_mono A (h A)

/-! ## 6. No coherence condition: the missing 2-cell is unique when it exists -/

/-- Parallel 2-cells between strong transformations into a representable etale stack are
equal: the fibers of a representable stack are discrete categories, so every component of
a modification is a morphism of a discrete category and is unique. -/
instance S1827SubsingletonModRep {S : SchemeOverField S1726K}
    {W : EtaleStackPseudofunctor S1726K}
    (a b : Pseudofunctor.StrongTrans W (S1743Y S)) : Subsingleton (a ⟶ b) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (S1801SubsingletonHom₂Discrete (a.app U) (b.app U)).elim _ _

/-- **The missing 2-cell is unique when it exists.**  The apex `P = Y(S_A)` of the
recorded square is representable, so its hom-categories are thin: the gap is the
*existence* of the unit 2-cell, not the coherence of a chosen one. -/
theorem S1827Unit_hom_unique (A : S1728Cover)
    (e1 e2 : Iso (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) :
    e1.hom = e2.hom :=
  Subsingleton.elim _ _

/-! ## 7. The refutation: the recorded witness does not imply the missing coherence -/

/-- The ess-surjectivity shape of `S1827ConeEssSurj` for an arbitrary square and witness;
this is definitionally S1801's schema. -/
def S1827EssSurjOf {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W)
    (f : Pseudofunctor.StrongTrans W P),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toX) c.toX) →
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f sq.toY) c.toY) →
        Nonempty (Iso f (w.lift W c))

/-- The ess-surjectivity shape is S1801's schema. -/
theorem S1827EssSurjOf_iff_S1801 {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) :
    S1827EssSurjOf sq w ↔ S1801EssSurjOf S1726K sq w :=
  Iff.rfl

/-- **Refutation, in the shape used here.**  The recorded `TwoPullbackWitness` fields do
not imply the missing coherence for an arbitrary square: S1801's degenerate square
satisfies every recorded field and its cone comparison is not essentially surjective. -/
theorem S1827EssSurjNotFromWitness :
    ¬ (∀ (P X Y Z : EtaleStackPseudofunctor S1726K)
        (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness),
        S1827EssSurjOf sq w) := by
  intro h
  exact S1801NoGenericEssSurj S1726K
    (fun P X Y Z sq w => (S1827EssSurjOf_iff_S1801 sq w).mp (h P X Y Z sq w))

/-- The failure is the non-existence of a 2-cell, not the incoherence of a given one: in
the degenerate model no 2-cell from the identity to the constant lift exists at all. -/
theorem S1827WitnessNotIso :
    ¬ Nonempty (Iso
      (Pseudofunctor.StrongTrans.id (S1801TwoStack S1726K))
      (S1801ConstZero S1726K (S1801TwoStack S1726K))) :=
  S1801DegenerateNotIso S1726K

/-! ## 8. Checks -/

#check S1827RecordedCone
#check S1827Comparison
#check S1827Comparison_def
#check S1827Comparison_toX
#check S1827Comparison_toY
#check S1827SquareMap
#check S1827ComparisonMap
#check S1827SquareMap_apex_unique
#check S1827Comparison_inverse_unique
#check S1827ComparisonQuasiEquiv
#check S1827Comparison_counit
#check S1827ComparisonQuasiEquiv_of_unit
#check S1827Unit_of_comparisonQuasiEquiv
#check S1827ComparisonQuasiEquiv_iff_unit
#check S1827ComparisonQuasiEquiv_iff_end
#check S1827ConeEssSurj
#check S1827ConeEssSurj_iff_liftEssSurj
#check S1827ComparisonQuasiEquiv_of_coneEssSurj
#check S1827ConeEssSurj_of_comparisonQuasiEquiv
#check S1827ComparisonQuasiEquiv_iff_coneEssSurj
#check S1827ComparisonQuasiEquiv_iff_recordedActual
#check S1827MissingCharacterisation
#check S1827FirstMissing
#check S1827FirstMissing_iff_S1804
#check S1827FirstMissing_iff_S1756
#check S1827FirstMissing_iff_sourceRetraction
#check S1827FirstMissing_iff_S1758
#check S1827FirstMissing_iff_comparisonEquiv
#check S1827ComparisonQuasiEquiv_of_firstMissing
#check S1827FirstMissing_to_S1804
#check S1827FirstMissing_to_S1756
#check S1827FirstMissing_to_sourceRetraction
#check S1827FirstMissing_to_S1758
#check S1827FirstMissing_to_sourceRepresentableAll
#check S1827FirstMissing_closure
#check S1827ComparisonQuasiEquiv_of_mono
#check S1827ComparisonQuasiEquiv_of_monoAll
#check S1827StackEquivOfComparison
#check S1827SourceRepresentable_of_comparisonQuasiEquiv
#check S1827SourceRepresentableAll_of_comparisonEquiv
#check S1827Unit_hom_unique
#check S1827EssSurjOf
#check S1827EssSurjNotFromWitness
#check S1827WitnessNotIso

#print axioms S1827Comparison_inverse_unique
#print axioms S1827SquareMap_apex_unique
#print axioms S1827Comparison_counit
#print axioms S1827ComparisonQuasiEquiv_of_unit
#print axioms S1827Unit_of_comparisonQuasiEquiv
#print axioms S1827ComparisonQuasiEquiv_iff_unit
#print axioms S1827ComparisonQuasiEquiv_iff_end
#print axioms S1827ComparisonQuasiEquiv_of_coneEssSurj
#print axioms S1827ConeEssSurj_of_comparisonQuasiEquiv
#print axioms S1827ComparisonQuasiEquiv_iff_coneEssSurj
#print axioms S1827ComparisonQuasiEquiv_iff_recordedActual
#print axioms S1827MissingCharacterisation
#print axioms S1827FirstMissing_iff_S1756
#print axioms S1827FirstMissing_iff_sourceRetraction
#print axioms S1827FirstMissing_iff_S1758
#print axioms S1827FirstMissing_iff_comparisonEquiv
#print axioms S1827FirstMissing_closure
#print axioms S1827FirstMissing_to_sourceRepresentableAll
#print axioms S1827ComparisonQuasiEquiv_of_mono
#print axioms S1827Unit_hom_unique
#print axioms S1827EssSurjNotFromWitness
#print axioms S1827StackEquivOfComparison
#print axioms S1827SourceRepresentable_of_comparisonQuasiEquiv
#print axioms S1827SourceRepresentableAll_of_comparisonEquiv

end LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
