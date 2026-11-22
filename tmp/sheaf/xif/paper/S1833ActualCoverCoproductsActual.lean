/-
# S1833: actual S1728 cover category — finite coproducts and the exact first missing

## Setting

The actual category is

  `S1728ActualCategory11 : Category.{1,1} S1728Cover`,

the 2-isomorphism quotient of representable finite-etale stack maps to the S1726
orbicurve.  S1762 recorded `HasFiniteCoproducts` on this category as its exact
finite-coproduct obligation, together with the identity-cover terminal object.

## Verdict

`HasFiniteCoproducts` is **not** constructed unconditionally.  It is constructed
here from one explicit missing comparison, and the exact first missing is named:

  `S1833FirstMissing := S1743SliceFunctorMissing`,

the existence of a fully faithful, essentially surjective comparison functor
from the actual cover category to the affine finite-etale slice `S1733Slice`.
This statement is:

* exactly `S1733CoverSliceEquivalence` (S1733's target);
* equivalent to S1777's actual target equivalence and to the affine equivalence
  `S1728ActualCategory11 ≌ (CommAlgCat.FiniteEtale R')ᵒᵖ`;
* implied by S1743's stronger comparison structure
  `S1743CoverSliceComparison`, which also fixes the explicit object map.

Given this comparison, the coproduct side is fully constructive.  The algebra
category `(CommAlgCat.FiniteEtale R')ᵒᵖ` has finite coproducts unconditionally,
and transport along the equivalence yields:

* an initial object `S1833InitialObj` with `IsInitial`;
* binary coproducts `S1833CoproductObj A B` with the full universal property
  `IsColimit (S1833CoproductCofan ...)`;
* `HasFiniteCoproducts` on the actual category, by the standard
  initial + binary-coproduct construction.

Thus the coproduct construction itself is not missing: the exact first missing
is the stack-level cover/slice comparison.

## What is proved here

1. Conditional initial object, binary coproducts and finite coproducts on the
   actual `Category.{1,1}`, from an explicit affine equivalence.
2. The exact missing proposition and its equivalence with S1825/S1778/S1777/
   S1733/S1744-S1743 forms.
3. The conditional closure of S1762's
   `S1762FiniteCoproductObligationActual`.
4. A bonus: the same affine equivalence also gives pullbacks on the actual
   category, hence (with S1762's unconditional terminal object) finite limits,
   and therefore S1762's pre-Galois assembly with only the quotient and
   mono/direct-summand fields remaining.

## Direct disjoint-union route

The task also asks about the direct route: the disjoint union of the two cover
source stacks, finite etaleness of the inclusions, the initial object, and the
quotient universal property.  That route is not used here, and no part of it is
faked:

* Mathlib v4.32.2 has no closure of `Pseudofunctor.IsStack` under pointwise
  coproducts and no stackification/coproduct of Cat-valued stacks; the tree has
  no such construction either.
* S1831 proves that the recorded `TwoPullbackWitness` is too weak to give the
  genuine 2-universal property of the identity-point square; the missing
  geometric content is `S1831FirstMissing` / `S1743SourceRetraction`
  (a cover source is represented by its identity-point affine model, not merely
  a retract of it).
* Consequently the direct route is at present blocked at the source-stack
  coproduct/representability step, not at the category-theoretic coproduct
  universal property.

The affine route below bypasses this by doing all coproducts on the algebra
side, where they already exist, and transporting them across the one missing
comparison.

## Honest boundary

No `sorry`, no `axiom`, no `Shrink`, `ULift` or `PUnit`, and no fake
category, initial object, coproduct or limit.  Every construction is explicitly
conditional on `S1833FirstMissing` (equivalently the affine equivalence).  The
only axioms are `propext`, `Classical.choice` and `Quot.sound`.
-/

import tmp.sheaf.xif.paper.S1825GaloisOnSmallCategoryActual
import tmp.sheaf.xif.paper.S1777AffineCoverAlgebrasActual
import tmp.sheaf.xif.paper.S1762CoverLimitsActual
import tmp.sheaf.xif.paper.S1743CoverSliceActual

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1777AffineCoverAlgebrasActual
open LeanFormal.IUT.XiFPaper.S1778Category01ViaAlgebrasActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1825GaloisOnSmallCategoryActual

namespace LeanFormal.IUT.XiFPaper.S1833ActualCoverCoproductsActual

/-! ## 1. The actual category and the algebra side -/

/-- The actual S1728 cover type. -/
abbrev S1833Cover : Type 1 := S1728Cover

/-- The actual S1728 2-isomorphism quotient category, at `Category.{1,1}`. -/
abbrev S1833Category : Category.{1, 1} S1833Cover := S1728ActualCategory11

/-- The corrected algebra side: finite etale `R'`-algebras, opposite. -/
abbrev S1833Alg : Type 1 := S1779AlgR

/-- Its `Category.{0,1}` structure. -/
abbrev S1833AlgCategory : Category.{0, 1} S1833Alg := S1779AlgR_category

/-- An affine equivalence from the actual cover category to the algebra side. -/
abbrev S1833AffineEquiv : Type 1 :=
  @CategoryTheory.Equivalence S1833Cover S1833Alg S1833Category S1833AlgCategory

/-- The exact missing affine equivalence, as a proposition. -/
def S1833ActualAffineEquivalenceMissing : Prop := Nonempty S1833AffineEquiv

/-- The algebra side has finite coproducts unconditionally (Pi-algebras in
`FiniteEtaleAlg R'`; this is S1779's closure, not a hypothesis). -/
theorem S1833AlgHasFiniteCoproducts :
    @HasFiniteCoproducts S1833Alg S1833AlgCategory := inferInstance

/-! ## 2. Initial object and binary coproducts on the actual category

Transport from the algebra side.  The algebra side has an initial object and
binary coproducts as part of `HasFiniteCoproducts`; the equivalences preserve
colimits, so the same universal properties hold on the actual category. -/

/-- The initial object of the actual category, from an affine equivalence: it
is the image under the transported `HasInitial` instance. -/
theorem S1833HasInitial_of_affineEquiv
    (e : S1833AffineEquiv) : @HasInitial S1833Cover S1833Category :=
  @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    S1833Cover S1833Category S1833Alg S1833AlgCategory
    (Discrete PEmpty) inferInstance e.functor inferInstance inferInstance

/-- Binary coproducts of the actual category, from an affine equivalence. -/
theorem S1833HasBinaryCoproducts_of_affineEquiv
    (e : S1833AffineEquiv) : @HasBinaryCoproducts S1833Cover S1833Category :=
  @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    S1833Cover S1833Category S1833Alg S1833AlgCategory
    (Discrete WalkingPair) inferInstance e.functor inferInstance inferInstance

/-- The chosen initial object of the actual category. -/
noncomputable def S1833InitialObj (e : S1833AffineEquiv) : S1833Cover := by
  letI : @HasInitial S1833Cover S1833Category :=
    S1833HasInitial_of_affineEquiv e
  exact ⊥_ S1833Cover

/-- The universal property of the chosen initial object. -/
noncomputable def S1833InitialObj_isInitial (e : S1833AffineEquiv) :
    IsInitial (S1833InitialObj e) := by
  letI : @HasInitial S1833Cover S1833Category :=
    S1833HasInitial_of_affineEquiv e
  exact initialIsInitial

/-- The chosen binary coproduct object. -/
noncomputable def S1833CoproductObj
    (e : S1833AffineEquiv) (A B : S1833Cover) : S1833Cover := by
  letI : @HasBinaryCoproducts S1833Cover S1833Category :=
    S1833HasBinaryCoproducts_of_affineEquiv e
  exact A ⨿ B

/-- The binary cofan of the chosen coproduct. -/
noncomputable def S1833CoproductCofan
    (e : S1833AffineEquiv) (A B : S1833Cover) : BinaryCofan A B := by
  letI : @HasBinaryCoproducts S1833Cover S1833Category :=
    S1833HasBinaryCoproducts_of_affineEquiv e
  exact BinaryCofan.mk (coprod.inl : A ⟶ A ⨿ B) coprod.inr

/-- The universal property of the chosen binary coproduct: the cofan is a
colimit, i.e. the actual coproduct universal property. -/
noncomputable def S1833CoproductCofan_isColimit
    (e : S1833AffineEquiv) (A B : S1833Cover) :
    IsColimit (S1833CoproductCofan e A B) := by
  letI : @HasBinaryCoproducts S1833Cover S1833Category :=
    S1833HasBinaryCoproducts_of_affineEquiv e
  exact coprodIsCoprod A B

/-- Finite coproducts on the actual category, from an affine equivalence.
This is the standard construction of all finite coproducts from an initial
object and binary coproducts. -/
theorem S1833HasFiniteCoproducts_of_affineEquiv
    (e : S1833AffineEquiv) : @HasFiniteCoproducts S1833Cover S1833Category := by
  letI : @HasInitial S1833Cover S1833Category :=
    S1833HasInitial_of_affineEquiv e
  letI : @HasBinaryCoproducts S1833Cover S1833Category :=
    S1833HasBinaryCoproducts_of_affineEquiv e
  exact hasFiniteCoproducts_of_has_binary_and_initial

/-- Finite coproducts from the missing affine-equivalence proposition. -/
theorem S1833HasFiniteCoproducts_of_missing
    (h : S1833ActualAffineEquivalenceMissing) :
    @HasFiniteCoproducts S1833Cover S1833Category := by
  rcases h with ⟨e⟩
  exact S1833HasFiniteCoproducts_of_affineEquiv e

/-! ## 3. The exact first missing and its equivalent forms -/

/-- S1825's missing affine equivalence is exactly the same as the missing
equivalence at the actual `Category.{1,1}`. -/
theorem S1833ActualAffineEquivalenceMissing_iff_S1825 :
    S1833ActualAffineEquivalenceMissing ↔ S1825AffineEquivalenceMissing :=
  S1825AffineEquivalenceMissing_iff_quotient.symm

/-- The same missing input in S1778's form. -/
theorem S1833ActualAffineEquivalenceMissing_iff_S1778 :
    S1833ActualAffineEquivalenceMissing ↔ S1778AffineEquivalenceMissing :=
  S1833ActualAffineEquivalenceMissing_iff_S1825.trans
    S1825AffineEquivalenceMissing_iff_S1778

/-- The missing equivalence is exactly S1777's target equivalence.  This is
definitional: both are equivalences from the actual category to
`(CommAlgCat.FiniteEtale R')ᵒᵖ`. -/
theorem S1833ActualAffineEquivalenceMissing_iff_S1777 :
    S1833ActualAffineEquivalenceMissing ↔ S1777TargetEquivalence :=
  Iff.rfl

/-- The missing equivalence is exactly S1733's cover/slice equivalence. -/
theorem S1833ActualAffineEquivalenceMissing_iff_sliceEquivalence :
    S1833ActualAffineEquivalenceMissing ↔ S1733CoverSliceEquivalence :=
  (S1833ActualAffineEquivalenceMissing_iff_S1777.trans
    S1777TargetEquivalence_iff).trans S1777StackComparison_iff

/-- The exact minimal first missing, in S1743's functor form: a fully faithful
essentially surjective comparison functor from the actual cover category to the
affine finite-etale slice.  This is exactly the affine equivalence above. -/
def S1833FirstMissing : Prop := S1743SliceFunctorMissing

/-- The exact first missing is the affine equivalence. -/
theorem S1833FirstMissing_iff :
    S1833FirstMissing ↔ S1833ActualAffineEquivalenceMissing :=
  (S1833ActualAffineEquivalenceMissing_iff_sliceEquivalence.trans
    S1743SliceFunctorMissing_iff.symm).symm

/-- The exact first missing is S1733's slice equivalence. -/
theorem S1833FirstMissing_iff_sliceEquivalence :
    S1833FirstMissing ↔ S1733CoverSliceEquivalence :=
  S1743SliceFunctorMissing_iff

/-- S1743's stronger comparison structure (with the explicit object map)
supplies the exact first missing. -/
theorem S1833FirstMissing_of_comparison
    (h : S1743CoverSliceComparisonMissing) : S1833FirstMissing := by
  rcases h with ⟨d⟩
  exact S1743SliceFunctorMissing_iff.mpr
    (S1743CoverSliceEquivalence_of_comparison d)

/-- The exact first missing gives the affine equivalence. -/
theorem S1833ActualAffineEquivalenceMissing_of_firstMissing
    (h : S1833FirstMissing) : S1833ActualAffineEquivalenceMissing :=
  S1833FirstMissing_iff.mp h

/-- The exact first missing gives finite coproducts on the actual category. -/
theorem S1833HasFiniteCoproducts_of_firstMissing
    (h : S1833FirstMissing) :
    @HasFiniteCoproducts S1833Cover S1833Category := by
  rcases S1833ActualAffineEquivalenceMissing_of_firstMissing h with ⟨e⟩
  exact S1833HasFiniteCoproducts_of_affineEquiv e

/-- The exact first missing gives S1743's stronger comparison form directly. -/
theorem S1833HasFiniteCoproducts_of_comparison
    (h : S1743CoverSliceComparisonMissing) :
    @HasFiniteCoproducts S1833Cover S1833Category :=
  S1833HasFiniteCoproducts_of_firstMissing (S1833FirstMissing_of_comparison h)

/-! ## 4. The exact S1762 obligations

`S1762FiniteCoproductObligationActual` is literally `HasFiniteCoproducts` on
the actual S1728 category.  The theorem below closes it from the exact first
missing. -/

/-- S1762's finite-coproduct obligation, from the exact first missing. -/
theorem S1833FiniteCoproductObligationActual_of_firstMissing
    (h : S1833FirstMissing) : S1762FiniteCoproductObligationActual :=
  S1833HasFiniteCoproducts_of_firstMissing h

/-- The same obligation from S1743's explicit comparison structure. -/
theorem S1833FiniteCoproductObligationActual_of_comparison
    (h : S1743CoverSliceComparisonMissing) :
    S1762FiniteCoproductObligationActual :=
  S1833HasFiniteCoproducts_of_comparison h

/-! ## 5. Bonus: pullbacks and finite limits from the same comparison

The algebra side also has pullbacks (tensor products of finite etale algebras)
unconditionally.  Hence the affine equivalence closes S1762's pullback
obligation as well, and with S1762's unconditional terminal object the whole
finite-limit field. -/

/-- Pullbacks on the actual category, from an affine equivalence. -/
theorem S1833HasPullbacks_of_affineEquiv
    (e : S1833AffineEquiv) : @HasPullbacks S1833Cover S1833Category :=
  @CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
    S1833Alg S1833AlgCategory S1833Cover S1833Category
    WalkingCospan inferInstance e.functor inferInstance inferInstance

/-- S1762's pullback obligation, from the exact first missing. -/
theorem S1833PullbackObligationActual_of_firstMissing
    (h : S1833FirstMissing) : S1762PullbackObligationActual := by
  rcases S1833ActualAffineEquivalenceMissing_of_firstMissing h with ⟨e⟩
  exact S1833HasPullbacks_of_affineEquiv e

/-- Finite limits on the actual category, from an affine equivalence and
S1762's unconditional terminal object. -/
theorem S1833HasFiniteLimits_of_affineEquiv
    (e : S1833AffineEquiv) : @HasFiniteLimits S1833Cover S1833Category := by
  letI : @HasTerminal S1833Cover S1833Category := S1762HasTerminalS1728
  letI : @HasPullbacks S1833Cover S1833Category :=
    S1833HasPullbacks_of_affineEquiv e
  exact hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- S1736's finite-limit obligation, from the exact first missing. -/
theorem S1833FiniteLimitsObligation_of_firstMissing
    (h : S1833FirstMissing) :
    S1736ObligationFiniteLimits (F := S1726K) (X := S1726Orbicurve) := by
  rcases S1833ActualAffineEquivalenceMissing_of_firstMissing h with ⟨e⟩
  exact S1833HasFiniteLimits_of_affineEquiv e

/-! ## 6. Pre-Galois assembly with the coproduct and pullback fields discharged

S1762's assembly took the pullback and coproduct obligations as inputs.  The
exact first missing supplies both, so the actual PreGalois structure reduces to
the affine comparison plus the two genuinely remaining fields (quotients by
finite groups and mono/direct summand). -/

/-- The actual pre-Galois obligation, from the exact first missing, the
quotient field and the mono/direct-summand field. -/
theorem S1833PreGaloisCategoryOfFirstMissing
    (h : S1833FirstMissing)
    (hQuot : S1762FiniteGroupQuotientObligationActual)
    (hMono : S1762MonoDirectSummandObligationActual) :
    S1736ActualPreGaloisObligation (F := S1726K) (X := S1726Orbicurve) :=
  S1762PreGaloisCategoryOfRemainingInputs
    (S1833PullbackObligationActual_of_firstMissing h)
    (S1833FiniteCoproductObligationActual_of_firstMissing h) hQuot hMono

/-! ## 7. Axiom audit -/

#print axioms S1833AlgHasFiniteCoproducts
#print axioms S1833HasInitial_of_affineEquiv
#print axioms S1833HasBinaryCoproducts_of_affineEquiv
#print axioms S1833HasFiniteCoproducts_of_affineEquiv
#print axioms S1833HasFiniteCoproducts_of_missing
#print axioms S1833ActualAffineEquivalenceMissing_iff_S1825
#print axioms S1833ActualAffineEquivalenceMissing_iff_S1778
#print axioms S1833ActualAffineEquivalenceMissing_iff_sliceEquivalence
#print axioms S1833FirstMissing_iff
#print axioms S1833FirstMissing_of_comparison
#print axioms S1833HasFiniteCoproducts_of_firstMissing
#print axioms S1833HasFiniteCoproducts_of_comparison
#print axioms S1833FiniteCoproductObligationActual_of_firstMissing
#print axioms S1833HasPullbacks_of_affineEquiv
#print axioms S1833PullbackObligationActual_of_firstMissing
#print axioms S1833HasFiniteLimits_of_affineEquiv
#print axioms S1833FiniteLimitsObligation_of_firstMissing
#print axioms S1833PreGaloisCategoryOfFirstMissing

end LeanFormal.IUT.XiFPaper.S1833ActualCoverCoproductsActual
