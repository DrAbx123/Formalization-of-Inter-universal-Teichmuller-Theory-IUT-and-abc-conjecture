/-
# S1792: quotient covers for finite group actions on the actual S1728 cover category

## Target

For the actual S1728 category

  S1728CoverCategory11 : Category.{1,1} (OrbicurveFiniteEtaleCover S1726Orbicurve),

a finite group `G`, a cover `A`, and a functor

  D : SingleObj G ⥤ OrbicurveFiniteEtaleCover S1726Orbicurve,

construct a quotient cover `Q` and a colimiting cocone over `D`
(S1763's `S1763QuotientCoverRequired D`).

## Result of this file

The quotient is **not** constructed unconditionally.  No `sorry`, no axiom and
no fake colimit is introduced.  The file records the precise two inputs that
are missing in the tree, proves that they are sufficient, and constructs the
quotient object and its colimiting cocone *from those inputs*.

The two missing inputs are:

1. `S1792CoverSliceEquivalence`: an equivalence between the actual S1728
   2-isomorphism-quotient cover category and the affine finite-etale slice
   `S1733Slice` over the S1726 base.  This is the comparison studied in
   S1743/S1755/S1757/S1758.  Its remaining two-pullback half is
   `S1758FirstMissing`; `S1784LiftEssSurj` is the stronger cone-level form used
   by S1787, and `S1787LiftFunctorial` is the extra functoriality needed for the
   strict model comparison.

2. `S1792AffineQuotientColimits`: the affine finite-etale slice has colimits
   of shape `SingleObj G` for every finite group `G`, i.e. the quotient
   `Spec (A^G)` of a finite etale algebra by a finite group action is the
   colimit in the affine slice.  In the equivalent finite-etale-cover model
   the tree contains the quotient *cover object* and the invariant cocone
   (`ABCBridge.AffineBaseFiniteEtaleQuotients.quotientCoverOfDiagram`,
   `...actionCoconeOfDiagram`) and the algebra-level fixed-point theorem
   (`FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale`), but not
   the affine universal property / `IsColimit`; the exact residual is recorded
   in the affine development as `GlobalQuotientCoconeResidual` /
   `GlobalQuotientProviderResidual`.

## Quotient-stack route

The task also allows an orbi/etale stack quotient.  That route is not available
either: Mathlib v4.32.2 and this tree have no quotient-stack / 2-colimit API for
a finite group action on a category-valued etale stack, and no
representable-finite-etale stabilization theorem for such a quotient.  S1761
records the absence of algebraic/DM stack, atlas, stack-quotient and
stackification APIs.  The existing `Iut.OrbicurveSignQuotientWitness` is a
different quotient (of the base orbicurve, not of a cover), and S1763 already
explains why it is not a constructor of the cover quotient.

Thus the exact first missing for the quotient-cover target is
`S1792CoverSliceEquivalence` (the comparison half), followed by
`S1792AffineQuotientColimits` (the affine quotient universal property).  The
file proves:

  S1792CoverSliceEquivalence → S1792AffineQuotientColimits →
    S1763FiniteGroupQuotientData

and, for each diagram, an actual `Q`, cocone and `IsColimit` under those
inputs.  The unconditional trivial-action and terminal-action cases of S1763
are re-exported and checked, so the conditional construction does not replace
or weaken them.

## Verification

Compiled with `lake env lean`.  Axioms of every declaration are exactly
`propext`, `Classical.choice`, `Quot.sound`.
-/

import tmp.sheaf.xif.paper.S1763CoverQuotientsActual
import tmp.sheaf.xif.paper.S1733EssentiallySmallCoversActual
import Mathlib.CategoryTheory.Adjunction.Limits

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1792QuotientCoverActual

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual
open LeanFormal.IUT.XiFPaper.S1763CoverQuotientsActual

/-! ## 0. The actual category, the slice, and the two missing inputs -/

/-- The actual S1728 category on the S1726 cover type. -/
local instance s1792ActualCategory : Category.{1, 1} S1728Cover :=
  S1728ActualCategory11

/-- The affine finite-etale slice over the S1726 base, exactly S1733's slice. -/
abbrev S1792Slice : Type 1 := S1733Slice

/-- The actual cover type is the S1728 cover type. -/
abbrev S1792Cover : Type 1 := S1728Cover

/-- The action functor of a finite group on an actual cover. -/
abbrev S1792Action (G : Type 1) [Group G] : Type 1 :=
  SingleObj G ⥤ S1792Cover

/-- The exact per-diagram quotient requirement, restated from S1763.  A
witness consists of an actual cover `Q` and a colimiting cocone over `D`. -/
abbrev S1792QuotientData (G : Type 1) [Group G]
    (D : S1792Action G) : Type 1 :=
  ColimitCocone D

/-- The exact per-diagram proposition. -/
def S1792QuotientCoverRequired (G : Type 1) [Group G] (D : S1792Action G) :
    Prop :=
  Nonempty (S1792QuotientData G D)

/-- **First missing input.**  The comparison equivalence between the actual
S1728 2-isomorphism-quotient cover category and the affine finite-etale slice
over the S1726 base.  This is the comparison whose object map is `S1743Object`
and whose remaining two-pullback half is `S1758FirstMissing`. -/
def S1792CoverSliceEquivalence : Prop :=
  Nonempty (S1792Cover ≌ S1792Slice)

/-- **Second missing input.**  Quotients by finite groups in the affine
finite-etale slice: for every finite group `G`, the slice has colimits of shape
`SingleObj G`.  This is the affine `A ↦ A^G` universal property; the tree has
the quotient object and the invariant cocone but not this `IsColimit`. -/
def S1792AffineQuotientColimits : Prop :=
  ∀ (G : Type 1) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) S1792Slice

/-- The exact first missing datum, named. -/
abbrev S1792FirstMissing : Prop := S1792CoverSliceEquivalence

/-- The exact second missing datum, named. -/
abbrev S1792SecondMissing : Prop := S1792AffineQuotientColimits

/-- The two exact inputs, bundled. -/
def S1792QuotientInputs : Prop :=
  S1792FirstMissing ∧ S1792SecondMissing

/-- The two inputs are exactly the comparison plus the affine colimit. -/
theorem S1792QuotientInputs_iff :
    S1792QuotientInputs ↔
      S1792CoverSliceEquivalence ∧ S1792AffineQuotientColimits :=
  Iff.rfl

/-! ## 1. Transport of finite-group colimits across the comparison -/

/-- If the actual cover category is equivalent to the affine slice and the
slice has finite-group quotient colimits, then the actual cover category has
finite-group quotient colimits.  This is the genuine transport step: no
colimit is fabricated; the affine colimit is moved along the equivalence. -/
theorem S1792HasColimitsOfShape_of_sliceEquivalence
    (E : S1792Cover ≌ S1792Slice)
    (hAff : S1792AffineQuotientColimits)
    (G : Type 1) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) S1792Cover := by
  letI : HasColimitsOfShape (SingleObj G) S1792Slice := hAff G
  haveI : E.functor.IsEquivalence := inferInstance
  exact Adjunction.hasColimitsOfShape_of_equivalence
    (J := SingleObj G) E.functor

/-- The per-diagram quotient cover requirement from the two exact inputs. -/
theorem S1792QuotientCoverRequired_of_sliceEquivalence
    (E : S1792Cover ≌ S1792Slice)
    (hAff : S1792AffineQuotientColimits)
    (G : Type 1) [Group G] [Finite G]
    (D : S1792Action G) :
    S1792QuotientCoverRequired G D := by
  letI : HasColimitsOfShape (SingleObj G) S1792Cover :=
    S1792HasColimitsOfShape_of_sliceEquivalence E hAff G
  letI : HasColimit D := HasColimitsOfShape.has_colimit D
  exact HasColimit.exists_colimit

/-- The same theorem in the bundled-input form. -/
theorem S1792QuotientCoverRequired_of_inputs
    (h : S1792QuotientInputs)
    (G : Type 1) [Group G] [Finite G]
    (D : S1792Action G) :
    S1792QuotientCoverRequired G D :=
  S1792QuotientCoverRequired_of_sliceEquivalence
    (Classical.choice h.1) h.2 G D

/-! ## 2. The quotient object and its colimiting cocone, from the inputs

The quotient cover and the cocone are chosen from the transported colimit
theorem.  They are genuine objects of the actual category and a genuine
`IsColimit`; the only non-constructive step is the choice of a colimit cocone,
which is exactly the classical choice used throughout Mathlib's limits API. -/

/-- The quotient cover `Q` for a finite-group action, from the two exact
inputs. -/
noncomputable def S1792QuotientCover
    (E : S1792Cover ≌ S1792Slice)
    (hAff : S1792AffineQuotientColimits)
    (G : Type 1) [Group G] [Finite G]
    (D : S1792Action G) : S1792Cover :=
  (Classical.choice
    (S1792QuotientCoverRequired_of_sliceEquivalence E hAff G D)).cocone.pt

/-- The colimiting cocone over `D` with point `S1792QuotientCover`. -/
noncomputable def S1792QuotientCocone
    (E : S1792Cover ≌ S1792Slice)
    (hAff : S1792AffineQuotientColimits)
    (G : Type 1) [Group G] [Finite G]
    (D : S1792Action G) : Cocone D :=
  (Classical.choice
    (S1792QuotientCoverRequired_of_sliceEquivalence E hAff G D)).cocone

/-- The quotient cocone is colimiting. -/
noncomputable def S1792QuotientCocone_isColimit
    (E : S1792Cover ≌ S1792Slice)
    (hAff : S1792AffineQuotientColimits)
    (G : Type 1) [Group G] [Finite G]
    (D : S1792Action G) :
    IsColimit (S1792QuotientCocone E hAff G D) :=
  (Classical.choice
    (S1792QuotientCoverRequired_of_sliceEquivalence E hAff G D)).isColimit

/-- The point of the quotient cocone is the quotient cover. -/
@[simp] theorem S1792QuotientCocone_pt
    (E : S1792Cover ≌ S1792Slice)
    (hAff : S1792AffineQuotientColimits)
    (G : Type 1) [Group G] [Finite G]
    (D : S1792Action G) :
    (S1792QuotientCocone E hAff G D).pt =
      S1792QuotientCover E hAff G D := rfl

/-- The bundled quotient datum. -/
noncomputable def S1792QuotientDatum
    (E : S1792Cover ≌ S1792Slice)
    (hAff : S1792AffineQuotientColimits)
    (G : Type 1) [Group G] [Finite G]
    (D : S1792Action G) : S1792QuotientData G D :=
  ⟨S1792QuotientCocone E hAff G D,
    S1792QuotientCocone_isColimit E hAff G D⟩

/-! ## 3. The global quotient data -/

/-- The global finite-group quotient obligation for the S1726 orbicurve, from
the comparison and the affine quotient colimits.  This is exactly S1763's
`S1763FiniteGroupQuotientData`, with the actual S1726 field and orbicurve. -/
theorem S1792FiniteGroupQuotientData_of_inputs
    (E : S1792Cover ≌ S1792Slice)
    (hAff : S1792AffineQuotientColimits) :
    S1763FiniteGroupQuotientData S1726K S1726Orbicurve := by
  intro G _ _ D
  exact S1792QuotientCoverRequired_of_sliceEquivalence E hAff G D

/-- The same global data from the bundled inputs. -/
theorem S1792FiniteGroupQuotientData_of_bundled
    (h : S1792QuotientInputs) :
    S1763FiniteGroupQuotientData S1726K S1726Orbicurve := by
  rcases h with ⟨hE, hAff⟩
  exact S1792FiniteGroupQuotientData_of_inputs
    (Classical.choice (show Nonempty (S1792Cover ≌ S1792Slice) from hE)) hAff

/-! ## 4. The unconditional cases already available in S1763

These are not new proofs; they are re-exported to show that the conditional
construction of Section 2 does not replace or weaken the cases that are already
unconditional, and to keep the exact boundary visible. -/

/-- The trivial action of any finite group on any cover has a genuine colimit,
namely the cover itself. -/
theorem S1792TrivialActionQuotient
    (G : Type 1) [Group G] [Finite G]
    (A : S1792Cover) :
    Nonempty (ColimitCocone ((Functor.const (SingleObj G)).obj A)) :=
  S1763TrivialActionQuotient (F := S1726K) (X := S1726Orbicurve) G A

/-- The trivial-action colimit cocone is `constCocone` at the connected index
category `SingleObj G`. -/
noncomputable def S1792TrivialActionQuotientCocone
    (G : Type 1) [Group G] [Finite G]
    (A : S1792Cover) :
    IsColimit (Limits.constCocone (SingleObj G) A) :=
  S1763TrivialActionQuotientCocone (F := S1726K) (X := S1726Orbicurve) G A

/-- Conditional quotient for an action on the terminal cover, using exactly
S1736's identity-finite-etale input.  This is S1763's terminal case. -/
theorem S1792TerminalActionQuotient
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber))
    (G : Type 1) [Group G] [Finite G]
    (D : S1792Action G)
    (hobj : ∀ j, D.obj j =
      S1736TerminalCover (F := S1726K) (X := S1726Orbicurve) h) :
    Nonempty (ColimitCocone D) :=
  S1763TerminalActionQuotient (F := S1726K) (X := S1726Orbicurve)
    h G D hobj

/-! ## 5. The quotient-stack route is not a constructor

The tree has no quotient-stack API.  The following checks record the two
existing objects that could be mistaken for one:

* `Iut.OrbicurveSignQuotientWitness` is the quotient of the *base* orbicurve by
  its sign action, not the quotient of a cover by a finite group action.
* S1763's `S1763QuotientCoverRequired` is the target itself, not a
  construction.

No inhabitant of either is used as a quotient cover. -/

/-- The sign-quotient witness requires an invariant morphism of the base
orbicurve.  This is S1763's re-export, included to show its type; it is not a
cover-quotient constructor. -/
abbrev S1792SignQuotientWitnessRequired
    (F : Type) [Field F] (X : Iut.HyperbolicOrbicurve F) : Type 1 :=
  S1763SignQuotientWitnessRequired F X

/- The sign-quotient witness descends invariant base maps (S1763's
`S1763SignQuotientWitness_descend`); again this is the base quotient, not a
quotient of a cover.  It is only checked at the end of the file and is not used
as a constructor. -/

/-! ## 6. Status and axiom audit -/

#check S1792Cover
#check S1792Slice
#check S1792Action
#check S1792QuotientData
#check S1792QuotientCoverRequired
#check S1792CoverSliceEquivalence
#check S1792AffineQuotientColimits
#check S1792FirstMissing
#check S1792SecondMissing
#check S1792QuotientInputs
#check S1792QuotientInputs_iff
#check S1792HasColimitsOfShape_of_sliceEquivalence
#check S1792QuotientCoverRequired_of_sliceEquivalence
#check S1792QuotientCoverRequired_of_inputs
#check S1792QuotientCover
#check S1792QuotientCocone
#check S1792QuotientCocone_isColimit
#check S1792QuotientCocone_pt
#check S1792QuotientDatum
#check S1792FiniteGroupQuotientData_of_inputs
#check S1792FiniteGroupQuotientData_of_bundled
#check S1792TrivialActionQuotient
#check S1792TrivialActionQuotientCocone
#check S1792TerminalActionQuotient
#check S1792SignQuotientWitnessRequired
#check S1763SignQuotientWitness_descend

#print axioms S1792QuotientInputs_iff
#print axioms S1792HasColimitsOfShape_of_sliceEquivalence
#print axioms S1792QuotientCoverRequired_of_sliceEquivalence
#print axioms S1792QuotientCoverRequired_of_inputs
#print axioms S1792QuotientCocone_isColimit
#print axioms S1792QuotientDatum
#print axioms S1792FiniteGroupQuotientData_of_inputs
#print axioms S1792FiniteGroupQuotientData_of_bundled
#print axioms S1792TrivialActionQuotient
#print axioms S1792TrivialActionQuotientCocone
#print axioms S1792TerminalActionQuotient

end LeanFormal.IUT.XiFPaper.S1792QuotientCoverActual
