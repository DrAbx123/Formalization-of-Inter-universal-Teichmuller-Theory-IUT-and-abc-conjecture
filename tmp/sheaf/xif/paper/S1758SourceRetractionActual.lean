/-
# S1758: the missing half of stack representability at the identity point

## Question

S1743 reduced the comparison between the actual finite-etale cover category of
the S1726 D6 orbicurve and the S1733 affine finite-etale slice to two
statements.  The first, recorded there as `S1743SourceRetraction`, asks:
for every cover `A` there is a strong transformation

    inv : A.source ⟶ Y (S1733Model A)

whose composite with the identity-point comparison `toSource` is
2-isomorphic to the identity of the representable model stack:

    vcomp (toSource) (inv)  ≅  id_{Y (S1733Model A)} .

The opposite composite is already proved unconditionally in S1743
(`S1743ModelSection`): the two-pullback lift `S1743Lift A` of the
identity cone satisfies `vcomp (S1743Lift A) toSource ≅ id`.

## What this file does

The identity-point base-change presentation
`(A.finiteEtale.baseChange S1726AffineOver S1733BasePoint)` is the
presentation supplied by the finite-etale representability datum stored in the
cover.  Its two-pullback witness supplies, for every apex `W`,

* a lift of every cone over the square (`lift`),
* the two comparison 2-isomorphisms (`liftToX`, `liftToY`),
* the induced 2-cell on cone morphisms (`liftTwoCell`),
* 2-cell extensionality (`twoCell_ext`).

This file adds the following, all unconditionally:

1. The *tautological cone* `S1758Cone A f` over the identity-point square
   associated with an actual 1-cell `f : W ⟶ Y (S1733Model A)`, together
   with the comparison lemmas that are derivable from the witness:
   - 2-cells into the model are determined by their whiskering along
     `toSource` (`S1758TwoCell_ext_toSource`);
   - the compatibility of cone morphisms is automatic, because the base corner
     of the identity-point square is the *representable* stack of `Spec R'`
     (`S1758ConeMorphism_compatibility_automatic`);
   - modifications between strong transformations into a representable stack
     are subsingletons (`S1758Modification_subsingleton`).

2. Explicit *formulas* for the two whiskerings of a candidate inverse
   2-cell `(vcomp toSource inv) ⟶ id`: the canonical 2-isomorphisms
   `S1758WhiskerX` and `S1758WhiskerY`, built from the comparison
   2-cells `liftToX` of the identity cone, `liftToY` of the identity
   cone, the base-change comparison `commutes`, and the unitors.  They are
   the components of the cone isomorphism used in item 5; what is missing is
   the *existence* of the inverse 2-cell, not a choice of formula.

3. The *uniqueness* of the inverse 2-cell: any two 2-cells
   `(vcomp toSource inv) ⟶ id` are equal, and any two candidate
   retraction isomorphisms are equal (`S1758InverseTwoCell_unique`,
   `S1758RetractionIso_unique`).  So, whenever the retraction half exists, it
   is unique.

4. The exact missing statement, isolated as `S1758LiftConeIso A` /
   `S1758FirstMissing`: *1-cell uniqueness* of the two-pullback, i.e. the
   lift of the tautological cone of an actual 1-cell is 2-isomorphic to that
   1-cell.  This is the counit half of the comparison functor from 1-cells into
   the pullback to cones over the square; the witness supplies only its
   object-level version (`lift` together with `liftToX`/`liftToY`), its
   morphism-level version (`liftTwoCell`) and faithfulness
   (`twoCell_ext`), but not the counit.  The extra field is packaged as
   `S1758LiftConeField`; it is not a field of the recorded witness.

5. The reduction: the missing statement implies `S1743SourceRetraction`
   (`S1758SourceRetraction_of_firstMissing`).  The proof is explicit: the
   cones of `r ≫ s` and of the identity are isomorphic (by the formulas above,
   via `liftTwoCell`), and 1-cell uniqueness transports the lift of the
   first cone to `r ≫ s` and the lift of the second to the identity, giving

    r ≫ s  ≅  lift (cone (r ≫ s))  ≅  lift (cone 1)  ≅  1 .

6. The *converse*, and exactness of the missing statement
   (`S1758LiftConeIso_of_retraction`,
   `S1758FirstMissing_iff_retractionAtLift`): from the canonical retraction
   `r ≫ s ≅ 1` one reconstructs 1-cell uniqueness for *every* 1-cell
   `f`, by the explicit chain

    lift (cone f) ≅ lift (cone f) ≫ 1 ≅ lift (cone f) ≫ (r ≫ s)
      ≅ (lift (cone f) ≫ r) ≫ s ≅ (f ≫ r) ≫ s ≅ f ≫ (r ≫ s) ≅ f ≫ 1 ≅ f .

   Therefore `S1758FirstMissing` is *equivalent* to the retraction half of
   stack representability at the canonical lift `S1743Lift A`.  So the missing
   statement is exactly the S1743 gap, neither stronger nor weaker.

## Honest boundary

The retraction `S1743SourceRetraction` is NOT proved unconditionally and no
inhabitant of the missing statement is constructed.  No `sorry`, no new axiom,
no `Shrink`/`ULift`/`PUnit`, and no fake 2-cell is used: the only axioms are
`propext`, `Classical.choice` and `Quot.sound`, inherited from the S1743
development.  The file records `S1743SourceRetraction` as missing, together with
the exact additional two-pullback statement needed to close it.
-/
import tmp.sheaf.xif.paper.S1743CoverSliceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1758SourceRetractionActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual

/-! ## 0. Uniqueness of 2-cells into a representable stack -/

/-- A natural transformation between functors into a discrete category is a
subsingleton.  This is the elementary reason why the base corner of the
identity-point square carries no information at the level of 2-cells. -/
theorem S1758NatTrans_discrete_subsingleton {C : Type*} [Category C] {α : Type}
    (F G : C ⥤ Discrete α) : Subsingleton (F ⟶ G) := by
  constructor
  intro a b
  apply CategoryTheory.NatTrans.ext
  funext X
  exact Subsingleton.elim _ _

/-- Modifications between strong transformations into a representable etale
stack are subsingletons: every component lands in a discrete category. -/
theorem S1758Modification_subsingleton {W : EtaleStackPseudofunctor S1726K}
    {S : SchemeOverField S1726K} (L L' : W ⟶ S1743Y S) :
    Subsingleton (L ⟶ L') := by
  constructor
  intro a b
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  apply CategoryTheory.Cat.Hom₂.ext
  haveI : Subsingleton ((L.app U).toFunctor ⟶ (L'.app U).toFunctor) :=
    S1758NatTrans_discrete_subsingleton _ _
  exact Subsingleton.elim _ _

/-- The same statement for the orbicurve stack itself, which is the
representable stack of the S1726 affine base. -/
theorem S1758Modification_subsingleton_stack {W : EtaleStackPseudofunctor S1726K}
    (L L' : W ⟶ S1726Orbicurve.stack.fiber) :
    Subsingleton (L ⟶ L') :=
  S1758Modification_subsingleton (S := S1726AffineOver) L L'

/-! ## 1. The identity-point presentation, abbreviated -/

/-- The comparison of the identity-point base change, to the cover source. -/
noncomputable abbrev S1758toSource (A : S1728Cover) :
    S1743ModelStack A ⟶ S1743Source A :=
  (S1743BaseChange A).toSource

/-- The projection of the identity-point base change, to the affine base. -/
noncomputable abbrev S1758projection (A : S1728Cover) :
    S1743ModelStack A ⟶ S1743Y S1726AffineOver :=
  (S1743BaseChange A).projectionMap.transformation

/-- The cover map to the orbicurve. -/
abbrev S1758Map (A : S1728Cover) :
    S1743Source A ⟶ S1726Orbicurve.stack.fiber :=
  A.map

/-- The lift of the identity cone, i.e. the *section* half of stack
representability, proved unconditionally in S1743. -/
noncomputable abbrev S1758Lift (A : S1728Cover) :
    S1743Source A ⟶ S1743ModelStack A :=
  S1743Lift A

/-- The first comparison 2-cell of the lift of the identity cone:
`s ≫ toSource ≅ id`. -/
noncomputable def S1758SectionIso (A : S1728Cover) :
    Iso (S1758Lift A ≫ S1758toSource A) (𝟙 (S1743Source A)) :=
  (S1743BaseChange A).isPullback.liftToX (S1743Source A) (S1743IdentityCone A)

/-- The second comparison 2-cell of the lift of the identity cone:
`s ≫ projection ≅ map`. -/
noncomputable def S1758SectionBaseIso (A : S1728Cover) :
    Iso (S1758Lift A ≫ S1758projection A) (S1758Map A) :=
  (S1743BaseChange A).isPullback.liftToY (S1743Source A) (S1743IdentityCone A)

/-- The base-change comparison 2-cell, written against the projection (the
second leg of the square is the identity of the representable base, and the
right unitor removes it). -/
noncomputable def S1758CommutesIso (A : S1728Cover) :
    Iso (S1758toSource A ≫ S1758Map A) (S1758projection A) :=
  (S1743BaseChange A).commutes ≪≫
    Pseudofunctor.StrongTrans.rightUnitor (S1758projection A)

/-! ## 2. The formulas for the whiskerings of a candidate inverse 2-cell

Suppose `β : (toSource ≫ inv) ⟶ id` were a 2-cell.  Its two
whiskerings are 2-cells

  `β ▷ toSource : ((toSource ≫ inv) ≫ toSource) ⟶ (id ≫ toSource)`
  `β ▷ projection : ((toSource ≫ inv) ≫ projection) ⟶ (id ≫ projection)`

The two definitions below are the canonical isomorphisms of those types, built
from the recorded comparison 2-cells.  They supply the components of the cone
isomorphism of Section 5.  They are not forced by the missing inverse 2-cell:
what is missing is that an inverse 2-cell exists at all. -/
noncomputable def S1758WhiskerX (A : S1728Cover) :
    Iso ((S1758toSource A ≫ S1758Lift A) ≫ S1758toSource A)
      (𝟙 (S1743ModelStack A) ≫ S1758toSource A) :=
  (Bicategory.associator (S1758toSource A) (S1758Lift A) (S1758toSource A)) ≪≫
    (Bicategory.whiskerLeftIso (S1758toSource A) (S1758SectionIso A)) ≪≫
      (Bicategory.rightUnitor (S1758toSource A)) ≪≫
        (Bicategory.leftUnitor (S1758toSource A)).symm

/-- The second formula: the whiskering of a candidate inverse 2-cell along the
projection of the identity-point base change. -/
noncomputable def S1758WhiskerY (A : S1728Cover) :
    Iso ((S1758toSource A ≫ S1758Lift A) ≫ S1758projection A)
      (𝟙 (S1743ModelStack A) ≫ S1758projection A) :=
  (Bicategory.associator (S1758toSource A) (S1758Lift A) (S1758projection A)) ≪≫
    (Bicategory.whiskerLeftIso (S1758toSource A) (S1758SectionBaseIso A)) ≪≫
      (S1758CommutesIso A) ≪≫
        (Bicategory.leftUnitor (S1758projection A)).symm

/-! ## 3. The tautological cone and 2-cell extensionality -/

/-- The tautological cone over the identity-point square associated with a
1-cell `f : W ⟶ Y (S1733Model A)`: its legs are `f` followed by the
two legs of the square. -/
noncomputable def S1758Cone (A : S1728Cover) {W : EtaleStackPseudofunctor S1726K}
    (f : W ⟶ S1743ModelStack A) : (S1743Square A).Cone W where
  toX := f ≫ S1758toSource A
  toY := f ≫ S1758projection A
  commutes :=
    (Bicategory.associator f (S1758toSource A) (S1758Map A)) ≪≫
      (Bicategory.whiskerLeftIso f (S1743BaseChange A).commutes) ≪≫
        (Bicategory.associator f (S1758projection A) S1733BasePoint).symm

/-- The lift of the tautological cone.  For `f = id` this is the lift of
the square itself; for `f = toSource ≫ S1758Lift A` it is the lift of the
cone produced by the section of the source. -/
noncomputable abbrev S1758LiftCone (A : S1728Cover) {W : EtaleStackPseudofunctor S1726K}
    (f : W ⟶ S1743ModelStack A) : W ⟶ S1743ModelStack A :=
  (S1743BaseChange A).isPullback.lift W (S1758Cone A f)

/-- The compatibility equation of a cone morphism is automatic for the
identity-point square: both sides are 2-cells into the representable base
stack. -/
theorem S1758ConeMorphism_compatibility_automatic (A : S1728Cover)
    {W : EtaleStackPseudofunctor S1726K}
    (source target : (S1743Square A).Cone W)
    (toX : source.toX ⟶ target.toX) (toY : source.toY ⟶ target.toY) :
    Pseudofunctor.StrongTrans.whiskerRight toX (S1743Square A).xToBase ≫
        target.commutes.hom =
      source.commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight toY (S1743Square A).yToBase := by
  haveI : Subsingleton ((source.toX ≫ (S1743Square A).xToBase) ⟶
      (target.toY ≫ (S1743Square A).yToBase)) :=
    S1758Modification_subsingleton_stack _ _
  exact Subsingleton.elim _ _

/-- 2-cell extensionality of the identity-point two-pullback, in the form used
below: a 2-cell into the affine model is determined by its whiskering along
`toSource` alone, because the other leg lands in a representable stack
and hence carries no 2-cell information. -/
theorem S1758TwoCell_ext_toSource (A : S1728Cover) {W : EtaleStackPseudofunctor S1726K}
    {first second : W ⟶ S1743ModelStack A} (alpha beta : first ⟶ second)
    (h : Pseudofunctor.StrongTrans.whiskerRight alpha (S1758toSource A) =
      Pseudofunctor.StrongTrans.whiskerRight beta (S1758toSource A)) : alpha = beta := by
  refine (S1743BaseChange A).isPullback.twoCell_ext (W := W) alpha beta h ?_
  change Pseudofunctor.StrongTrans.whiskerRight alpha (S1743Square A).toY =
    Pseudofunctor.StrongTrans.whiskerRight beta (S1743Square A).toY
  haveI : Subsingleton ((first ≫ (S1743Square A).toY) ⟶
      (second ≫ (S1743Square A).toY)) :=
    S1758Modification_subsingleton _ _
  exact Subsingleton.elim _ _

/-! ## 4. The exact missing statement -/

/-- **The first missing statement.**  1-cell uniqueness for the identity-point
two-pullback: the lift of the tautological cone of an actual 1-cell is
2-isomorphic to that 1-cell.  Equivalently, the counit of the comparison
functor `Hom(W, P) ⟶ Cone(W)` is an isomorphism.

The recorded `TwoPullbackWitness` does not contain this statement, and for
the identity-point square its source stack is not representable, so the 2-Yoneda
comparison of S1742 cannot replace it.  No inhabitant is constructed here. -/
def S1758LiftConeIso (A : S1728Cover) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K) (f : W ⟶ S1743ModelStack A),
    Nonempty (Iso (S1758LiftCone A f) f)

/-- The first missing statement uniformly over all covers. -/
def S1758FirstMissing : Prop := ∀ A : S1728Cover, S1758LiftConeIso A

/-- The extra two-pullback field that the identity-point presentation lacks,
packaged as data: for every 1-cell into the affine model, an isomorphism from
the lift of its tautological cone to the 1-cell itself. -/
structure S1758LiftConeField (A : S1728Cover) where
  /-- The counit isomorphism of the comparison at every tautological cone. -/
  iso : ∀ (W : EtaleStackPseudofunctor S1726K) (f : W ⟶ S1743ModelStack A),
    Iso (S1758LiftCone A f) f

/-- The propositional form of the missing field is the data-free statement. -/
theorem S1758LiftConeIso_iff_nonempty_field (A : S1728Cover) :
    S1758LiftConeIso A ↔ Nonempty (S1758LiftConeField A) :=
  ⟨fun h => ⟨⟨fun W f => (h W f).some⟩⟩,
    fun ⟨d⟩ W f => ⟨d.iso W f⟩⟩

/-- The retraction half of stack representability at the *canonical* lift: the
1-cell `S1743Lift A` produced by the two-pullback universal property is a
retraction of the comparison `toSource`.

This is the S1743 target specialised to the canonical lift.  It is *equivalent*
to `S1758FirstMissing` (`S1758FirstMissing_iff_retractionAtLift`), so
1-cell uniqueness is not a stronger requirement than the retraction asked for
in S1743. -/
def S1758RetractionAtLift : Prop :=
  ∀ A : S1728Cover,
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp (S1758toSource A) (S1758Lift A))
      (𝟙 (S1743ModelStack A)))

/-! ## 5. The comparison of the two tautological cones

The cone of `r ≫ s` and the cone of the identity are isomorphic, with
components given by the formulas of Section 2.  Consequently the
`liftTwoCell` supplies a 2-cell between the two lifts, and it is an
isomorphism. -/

/-- The cone morphism from the cone of `toSource ≫ S1758Lift A` to the
cone of the identity. -/
noncomputable def S1758ConeHom (A : S1728Cover) :
    (S1743Square A).ConeMorphism
      (S1758Cone A (S1758toSource A ≫ S1758Lift A))
      (S1758Cone A (𝟙 (S1743ModelStack A))) where
  toX := (S1758WhiskerX A).hom
  toY := (S1758WhiskerY A).hom
  compatibility := S1758ConeMorphism_compatibility_automatic A _ _ _ _

/-- The reverse cone morphism, with the inverse 2-cells. -/
noncomputable def S1758ConeHomInv (A : S1728Cover) :
    (S1743Square A).ConeMorphism
      (S1758Cone A (𝟙 (S1743ModelStack A)))
      (S1758Cone A (S1758toSource A ≫ S1758Lift A)) where
  toX := (S1758WhiskerX A).inv
  toY := (S1758WhiskerY A).inv
  compatibility := S1758ConeMorphism_compatibility_automatic A _ _ _ _

@[simp] theorem S1758ConeHom_toX (A : S1728Cover) :
    (S1758ConeHom A).toX = (S1758WhiskerX A).hom := rfl

@[simp] theorem S1758ConeHomInv_toX (A : S1728Cover) :
    (S1758ConeHomInv A).toX = (S1758WhiskerX A).inv := rfl

/-- The 2-cell between the two lifts supplied by `liftTwoCell`. -/
noncomputable def S1758LiftTwoCell (A : S1728Cover) :
    S1758LiftCone A (S1758toSource A ≫ S1758Lift A) ⟶
      S1758LiftCone A (𝟙 (S1743ModelStack A)) :=
  (S1743BaseChange A).isPullback.liftTwoCell (S1743ModelStack A)
    (S1758Cone A (S1758toSource A ≫ S1758Lift A))
    (S1758Cone A (𝟙 (S1743ModelStack A))) (S1758ConeHom A)

/-- The 2-cell in the reverse direction. -/
noncomputable def S1758LiftTwoCellInv (A : S1728Cover) :
    S1758LiftCone A (𝟙 (S1743ModelStack A)) ⟶
      S1758LiftCone A (S1758toSource A ≫ S1758Lift A) :=
  (S1743BaseChange A).isPullback.liftTwoCell (S1743ModelStack A)
    (S1758Cone A (𝟙 (S1743ModelStack A)))
    (S1758Cone A (S1758toSource A ≫ S1758Lift A)) (S1758ConeHomInv A)

/-- The `liftTwoCell` of the cone isomorphism is an isomorphism.  Both
composites are 2-cells between endomorphisms of the *representable* model
stack, hence subsingletons: the cancellation is forced by discreteness of the
target, and is not an extra coherence assumption. -/
theorem S1758LiftTwoCell_hom_inv_id (A : S1728Cover) :
    S1758LiftTwoCell A ≫ S1758LiftTwoCellInv A =
      𝟙 (S1758LiftCone A (S1758toSource A ≫ S1758Lift A)) := by
  haveI : Subsingleton
      (S1758LiftCone A (S1758toSource A ≫ S1758Lift A) ⟶
        S1758LiftCone A (S1758toSource A ≫ S1758Lift A)) :=
    S1758Modification_subsingleton (S := S1733Model A) _ _
  exact Subsingleton.elim _ _

/-- The reverse composite is the identity as well. -/
theorem S1758LiftTwoCell_inv_hom_id (A : S1728Cover) :
    S1758LiftTwoCellInv A ≫ S1758LiftTwoCell A =
      𝟙 (S1758LiftCone A (𝟙 (S1743ModelStack A))) := by
  haveI : Subsingleton
      (S1758LiftCone A (𝟙 (S1743ModelStack A)) ⟶
        S1758LiftCone A (𝟙 (S1743ModelStack A))) :=
    S1758Modification_subsingleton (S := S1733Model A) _ _
  exact Subsingleton.elim _ _

/-- The comparison of the two lifts is an isomorphism, unconditionally. -/
noncomputable def S1758LiftTwoCellIso (A : S1728Cover) :
    Iso (S1758LiftCone A (S1758toSource A ≫ S1758Lift A))
      (S1758LiftCone A (𝟙 (S1743ModelStack A))) where
  hom := S1758LiftTwoCell A
  inv := S1758LiftTwoCellInv A
  hom_inv_id := S1758LiftTwoCell_hom_inv_id A
  inv_hom_id := S1758LiftTwoCell_inv_hom_id A

/-! ## 6. The reduction: the missing statement implies the source retraction -/

/-- The source retraction for a single cover, from 1-cell uniqueness.  The
inverse 1-cell is the lift of the identity cone, and the inverse 2-cell is the
explicit composite

  `(toSource ≫ s) ≅ lift (cone (toSource ≫ s)) ≅ lift (cone 1) ≅ 1`. -/
theorem S1758SourceRetractionAt_of_liftConeIso (A : S1728Cover)
    (h : S1758LiftConeIso A) :
    ∃ inv : S1743Source A ⟶ S1743ModelStack A,
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp (S1758toSource A) inv)
        (𝟙 (S1743ModelStack A))) := by
  obtain ⟨e1⟩ := h (S1743ModelStack A) (S1758toSource A ≫ S1758Lift A)
  obtain ⟨e3⟩ := h (S1743ModelStack A) (𝟙 (S1743ModelStack A))
  refine ⟨S1758Lift A, ⟨?_⟩⟩
  exact e1.symm ≪≫ S1758LiftTwoCellIso A ≪≫ e3

/-- **The reduction.**  If the first missing statement (1-cell uniqueness for
the identity-point two-pullbacks of all covers) holds, then
`S1743SourceRetraction` holds. -/
theorem S1758SourceRetraction_of_firstMissing (h : S1758FirstMissing) :
    S1743SourceRetraction :=
  fun A => S1758SourceRetractionAt_of_liftConeIso A (h A)

/-- The first missing statement gives the canonical retraction. -/
theorem S1758RetractionAtLift_of_firstMissing (h : S1758FirstMissing) :
    S1758RetractionAtLift := by
  intro A
  obtain ⟨e1⟩ := h A (S1743ModelStack A) (S1758toSource A ≫ S1758Lift A)
  obtain ⟨e3⟩ := h A (S1743ModelStack A) (𝟙 (S1743ModelStack A))
  exact ⟨e1.symm ≪≫ S1758LiftTwoCellIso A ≪≫ e3⟩

/-- The canonical retraction gives `S1743SourceRetraction`: the inverse
1-cell is the canonical lift `S1743Lift A`. -/
theorem S1758SourceRetraction_of_retractionAtLift (h : S1758RetractionAtLift) :
    S1743SourceRetraction :=
  fun A => ⟨S1758Lift A, h A⟩

/-- Full stack representability of every cover by its affine model (S1743's
item (a)): the section half is S1743's unconditional `liftToX` of the identity
cone, and the retraction half is the canonical retraction. -/
theorem S1758SourceRepresentableAll_of_retractionAtLift
    (h : S1758RetractionAtLift) : S1743SourceRepresentableAll :=
  fun A =>
    ⟨S1758Lift A,
      ⟨(S1743BaseChange A).isPullback.liftToX (S1743Source A)
        (S1743IdentityCone A)⟩,
      h A⟩

/-- Full stack representability from the first missing statement. -/
theorem S1758SourceRepresentableAll_of_firstMissing (h : S1758FirstMissing) :
    S1743SourceRepresentableAll :=
  S1758SourceRepresentableAll_of_retractionAtLift
    (S1758RetractionAtLift_of_firstMissing h)

/-- Conversely, the canonical retraction implies full 1-cell uniqueness.  The
required inverse 2-cell is the explicit composite

  lift (cone f)
    ≅ lift (cone f) ≫ 1
    ≅ lift (cone f) ≫ (toSource ≫ s)
    ≅ (lift (cone f) ≫ toSource) ≫ s
    ≅ (f ≫ toSource) ≫ s
    ≅ f ≫ (toSource ≫ s)
    ≅ f ≫ 1
    ≅ f ,

which uses only the canonical retraction `toSource ≫ s ≅ 1` and the
comparison `liftToX` of the tautological cone. -/
theorem S1758LiftConeIso_of_retraction (A : S1728Cover)
    (h : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp (S1758toSource A) (S1758Lift A))
      (𝟙 (S1743ModelStack A)))) : S1758LiftConeIso A := by
  obtain ⟨rho⟩ := h
  intro W f
  refine ⟨?_⟩
  exact (Bicategory.rightUnitor (S1758LiftCone A f)).symm ≪≫
    (Bicategory.whiskerLeftIso (S1758LiftCone A f) rho.symm) ≪≫
      (Bicategory.associator (S1758LiftCone A f) (S1758toSource A) (S1758Lift A)).symm ≪≫
        (Bicategory.whiskerRightIso
          ((S1743BaseChange A).isPullback.liftToX W (S1758Cone A f))
            (S1758Lift A)) ≪≫
          (Bicategory.associator f (S1758toSource A) (S1758Lift A)) ≪≫
            (Bicategory.whiskerLeftIso f rho) ≪≫
              (Bicategory.rightUnitor f)

/-- **Exactness of the first missing statement.**  1-cell uniqueness for the
identity-point two-pullback is *equivalent* to the retraction half of stack
representability at the canonical lift.  Hence the missing statement is not a
strengthening of the S1743 target at the canonical lift; it is the same gap. -/
theorem S1758FirstMissing_iff_retractionAtLift :
    S1758FirstMissing ↔ S1758RetractionAtLift :=
  ⟨S1758RetractionAtLift_of_firstMissing,
    fun h => fun A => S1758LiftConeIso_of_retraction A (h A)⟩

/-! ## 7. Uniqueness of the inverse 2-cell

The formulas of Section 2 are not only necessary: up to the automatic
discreteness of the base corner, any two candidate inverse 2-cells agree. -/

/-- Any two 2-cells `(vcomp toSource inv) ⟶ id` are equal. -/
theorem S1758InverseTwoCell_unique (A : S1728Cover)
    {inv : S1743Source A ⟶ S1743ModelStack A}
    (beta beta' :
      Pseudofunctor.StrongTrans.vcomp (S1758toSource A) inv ⟶
        𝟙 (S1743ModelStack A)) : beta = beta' := by
  haveI : Subsingleton
      ((Pseudofunctor.StrongTrans.vcomp (S1758toSource A) inv) ⟶
        (𝟙 (S1743ModelStack A))) :=
    S1758Modification_subsingleton (S := S1733Model A) _ _
  exact Subsingleton.elim _ _

/-- Any two candidate retraction isomorphisms are equal. -/
theorem S1758RetractionIso_unique (A : S1728Cover)
    {inv : S1743Source A ⟶ S1743ModelStack A}
    (e e' : Iso (Pseudofunctor.StrongTrans.vcomp (S1758toSource A) inv)
      (𝟙 (S1743ModelStack A))) : e = e' := by
  apply Iso.ext
  exact S1758InverseTwoCell_unique A e.hom e'.hom

/-! ## 8. Checks and axiom footprint -/

#check S1758Modification_subsingleton
#check S1758ConeMorphism_compatibility_automatic
#check S1758TwoCell_ext_toSource
#check S1758Cone
#check S1758LiftCone
#check S1758WhiskerX
#check S1758WhiskerY
#check S1758LiftConeIso
#check S1758FirstMissing
#check S1758LiftConeField
#check S1758LiftConeIso_iff_nonempty_field
#check S1758ConeHom
#check S1758ConeHomInv
#check S1758LiftTwoCell
#check S1758LiftTwoCellInv
#check S1758LiftTwoCell_hom_inv_id
#check S1758LiftTwoCell_inv_hom_id
#check S1758LiftTwoCellIso
#check S1758SourceRetractionAt_of_liftConeIso
#check S1758SourceRetraction_of_firstMissing
#check S1758RetractionAtLift
#check S1758RetractionAtLift_of_firstMissing
#check S1758SourceRetraction_of_retractionAtLift
#check S1758SourceRepresentableAll_of_retractionAtLift
#check S1758SourceRepresentableAll_of_firstMissing
#check S1758LiftConeIso_of_retraction
#check S1758FirstMissing_iff_retractionAtLift
#check S1758InverseTwoCell_unique
#check S1758RetractionIso_unique

#print axioms S1758Modification_subsingleton
#print axioms S1758ConeMorphism_compatibility_automatic
#print axioms S1758TwoCell_ext_toSource
#print axioms S1758LiftTwoCell_hom_inv_id
#print axioms S1758LiftTwoCell_inv_hom_id
#print axioms S1758LiftTwoCellIso
#print axioms S1758SourceRetractionAt_of_liftConeIso
#print axioms S1758SourceRetraction_of_firstMissing
#print axioms S1758RetractionAtLift_of_firstMissing
#print axioms S1758SourceRetraction_of_retractionAtLift
#print axioms S1758SourceRepresentableAll_of_retractionAtLift
#print axioms S1758SourceRepresentableAll_of_firstMissing
#print axioms S1758LiftConeIso_of_retraction
#print axioms S1758LiftConeIso_iff_nonempty_field
#print axioms S1758FirstMissing_iff_retractionAtLift
#print axioms S1758InverseTwoCell_unique
#print axioms S1758RetractionIso_unique

end LeanFormal.IUT.XiFPaper.S1758SourceRetractionActual
