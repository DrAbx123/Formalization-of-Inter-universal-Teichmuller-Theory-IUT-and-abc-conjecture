/-
  Source stable reduction from Definition 3.1 and the actual Mathlib reduction.

  Definition 3.1 supplies, at every bad place, abstract stable, multiplicative and
  split-multiplicative reduction clauses plus a contracting q-parameter.  Mathlib
  supplies the actual minimal model and its reduction classes: good,
  multiplicative, additive, and split multiplicative.

  This file states an explicit bad-place/completion-place correspondence, proves
  the source stable reduction comparison from that correspondence, and records the
  actual reduction trichotomy.  The correspondence itself and any proper/regular/
  component data remain explicit hypotheses or residual, not fabricated objects.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiSourceSpecialFiberComparison
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiActualSpecialFiber
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiStableReductionFromSource

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiReductionSpecialFiber
open LeanFormal.IUT.SourcePsiActualSpecialFiber
open LeanFormal.IUT.SourcePsiActualMinimalSpecialFiber
open LeanFormal.IUT.SourcePsiSourceSpecialFiberComparison
open LeanFormal.IUT.SourcePsiResidueRingFinite
open LeanFormal.IUT.AdicCompletionFractionField
open LeanFormal.IUT.SourcePsiMinimalModelCriterion
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- Actual stable reduction: good, multiplicative, or additive reduction of the
actual minimal model. -/
def SourcePsiActualStableReduction : Prop :=
  SourcePsiActualGoodReduction S v ∨
    SourcePsiActualMultiplicativeReduction S v ∨
      SourcePsiActualAdditiveReduction S v

/-- The actual stable reduction trichotomy. -/
theorem SourcePsiActualStableReduction_trichotomy :
    SourcePsiActualStableReduction S v :=
  SourcePsiActualSpecialFiber_reduction_trichotomy S v

/-- Actual good reduction is stable. -/
theorem SourcePsiActualStableReduction_of_good
    (h : SourcePsiActualGoodReduction S v) :
    SourcePsiActualStableReduction S v :=
  Or.inl h

/-- Actual multiplicative reduction is stable. -/
theorem SourcePsiActualStableReduction_of_multiplicative
    (h : SourcePsiActualMultiplicativeReduction S v) :
    SourcePsiActualStableReduction S v :=
  Or.inr (Or.inl h)

/-- Actual additive reduction is stable. -/
theorem SourcePsiActualStableReduction_of_additive
    (h : SourcePsiActualAdditiveReduction S v) :
    SourcePsiActualStableReduction S v :=
  Or.inr (Or.inr h)

/-- Actual split multiplicative reduction implies actual multiplicative
reduction. -/
theorem SourcePsiActualSplit_imp_multiplicative
    (h : SourcePsiActualSplitMultiplicativeReduction S v) :
    SourcePsiActualMultiplicativeReduction S v :=
  h.toHasMultiplicativeReduction

/-- Actual split multiplicative reduction is stable. -/
theorem SourcePsiActualStableReduction_of_split
    (h : SourcePsiActualSplitMultiplicativeReduction S v) :
    SourcePsiActualStableReduction S v :=
  SourcePsiActualStableReduction_of_multiplicative S v
    (SourcePsiActualSplit_imp_multiplicative S v h)

/-- A bad-place/completion-place correspondence: a bad place, an actual source
special-fiber comparison over the completion residue field, and compatibility of
the source selected place with the bad-place inclusion. -/
structure SourcePsiBadPlaceCompletionCorrespondence where
  badPlace : S.badPlaces
  comparison : SourcePsiSourceSpecialFiberComparison S v
  place_compatible :
    comparison.place = S.reduction.partition.badIncluded badPlace

/-- Actual reduction type data for the completion place. -/
structure SourcePsiActualReductionTypeAtCompletion where
  good : Prop
  multiplicative : Prop
  additive : Prop
  splitMultiplicative : Prop
  good_iff : good ↔ SourcePsiActualGoodReduction S v
  multiplicative_iff : multiplicative ↔ SourcePsiActualMultiplicativeReduction S v
  additive_iff : additive ↔ SourcePsiActualAdditiveReduction S v
  split_iff : splitMultiplicative ↔ SourcePsiActualSplitMultiplicativeReduction S v
  stable_trichotomy : good ∨ multiplicative ∨ additive

/-- The actual reduction type data at the completion place. -/
def SourcePsiActualReductionTypeAtCompletion.ofActual :
    SourcePsiActualReductionTypeAtCompletion S v where
  good := SourcePsiActualGoodReduction S v
  multiplicative := SourcePsiActualMultiplicativeReduction S v
  additive := SourcePsiActualAdditiveReduction S v
  splitMultiplicative := SourcePsiActualSplitMultiplicativeReduction S v
  good_iff := Iff.rfl
  multiplicative_iff := Iff.rfl
  additive_iff := Iff.rfl
  split_iff := Iff.rfl
  stable_trichotomy := SourcePsiActualSpecialFiber_reduction_trichotomy S v

/-- Source stable-reduction comparison data at a supplied bad-place/completion
correspondence.  The source clauses are Definition 3.1 data; the comparison
fields are the actual correspondence hypotheses. -/
structure SourcePsiStableReductionComparisonData where
  correspondence : SourcePsiBadPlaceCompletionCorrespondence S v
  sourceReduction : SourcePsiDefinition31ReductionTypeData S correspondence.badPlace
  actualReduction : SourcePsiActualReductionTypeAtCompletion S v
  source_stable : S.reduction.stableReduction correspondence.badPlace
  actual_stable : SourcePsiActualStableReduction S v
  source_stable_iff_actual :
    S.reduction.stableReduction correspondence.badPlace ↔
      SourcePsiActualStableReduction S v
  source_multiplicative_iff_actual :
    S.reduction.multiplicativeReduction correspondence.badPlace ↔
      SourcePsiActualMultiplicativeReduction S v
  source_split_iff_actual :
    S.reduction.splitMultiplicativeReduction correspondence.badPlace ↔
      SourcePsiActualSplitMultiplicativeReduction S v

/-- From a stable-reduction comparison datum, the source stable reduction clause
gives actual stable reduction. -/
theorem SourcePsiStableReductionFromSource_stable_of_source
    (C : SourcePsiStableReductionComparisonData S v) :
    SourcePsiActualStableReduction S v :=
  C.source_stable_iff_actual.mp C.source_stable

/-- From the same datum, actual stable reduction gives the source stable
reduction clause. -/
theorem SourcePsiStableReductionFromSource_source_of_stable
    (C : SourcePsiStableReductionComparisonData S v)
    (h : SourcePsiActualStableReduction S v) :
    S.reduction.stableReduction C.correspondence.badPlace :=
  C.source_stable_iff_actual.mpr h

/-- Source split multiplicative reduction gives actual split multiplicative
reduction under the comparison. -/
theorem SourcePsiStableReductionFromSource_split_of_source
    (C : SourcePsiStableReductionComparisonData S v)
    (h : S.reduction.splitMultiplicativeReduction C.correspondence.badPlace) :
    SourcePsiActualSplitMultiplicativeReduction S v :=
  C.source_split_iff_actual.mp h

/-- Actual split multiplicative reduction gives the source split clause under the
comparison. -/
theorem SourcePsiStableReductionFromSource_source_split_of_actual
    (C : SourcePsiStableReductionComparisonData S v)
    (h : SourcePsiActualSplitMultiplicativeReduction S v) :
    S.reduction.splitMultiplicativeReduction C.correspondence.badPlace :=
  C.source_split_iff_actual.mpr h

/-- Source split multiplicative implies source multiplicative, and under the
comparison this is actual split implies actual multiplicative. -/
theorem SourcePsiStableReductionFromSource_comparison_split_chain
    (C : SourcePsiStableReductionComparisonData S v) :
    (S.reduction.splitMultiplicativeReduction C.correspondence.badPlace →
        S.reduction.multiplicativeReduction C.correspondence.badPlace) ∧
      (SourcePsiActualSplitMultiplicativeReduction S v →
        SourcePsiActualMultiplicativeReduction S v) :=
  ⟨fun h => S.reduction.reductionCompatibility C.correspondence.badPlace h,
    fun h => SourcePsiActualSplit_imp_multiplicative S v h⟩

/-- The actual reduction type is good, multiplicative, or additive, under the
comparison. -/
theorem SourcePsiStableReductionFromSource_actual_trichotomy
    (C : SourcePsiStableReductionComparisonData S v) :
    SourcePsiActualGoodReduction S v ∨
      SourcePsiActualMultiplicativeReduction S v ∨
        SourcePsiActualAdditiveReduction S v :=
  C.actualReduction.stable_trichotomy

/-- Exact source stable-reduction comparison statement: with a supplied
correspondence and comparison data, the source stable clauses and actual reduction
trichotomy agree. -/
theorem SourcePsiStableReductionFromSource_statement
    (C : SourcePsiStableReductionComparisonData S v) :
    SourcePsiActualStableReduction S v ∧
      (S.reduction.stableReduction C.correspondence.badPlace ↔
        SourcePsiActualStableReduction S v) ∧
        (S.reduction.splitMultiplicativeReduction C.correspondence.badPlace →
          SourcePsiActualSplitMultiplicativeReduction S v) :=
  ⟨SourcePsiStableReductionFromSource_stable_of_source S v C,
    C.source_stable_iff_actual,
    SourcePsiStableReductionFromSource_split_of_source S v C⟩

/-- Exact residual: a supplied bad-place/completion correspondence, comparison
data, and the missing proper/regular/component/stable geometric identification.
No inhabitant is asserted. -/
def SourcePsiStableReductionFromSourceResidual : Prop :=
  (∃ C : SourcePsiStableReductionComparisonData S v,
    S.reduction.splitMultiplicativeReduction C.correspondence.badPlace →
      SourcePsiActualSplitMultiplicativeReduction S v) ∧
    (∃ b : S.badPlaces, Nonempty (SourcePsiDefinition31ReductionTypeData S b))



/-- Correspondence projection: the source selected place is the included bad
place. -/
theorem SourcePsiBadPlaceCompletionCorrespondence_place
    (C : SourcePsiBadPlaceCompletionCorrespondence S v) :
    C.comparison.place = S.reduction.partition.badIncluded C.badPlace :=
  C.place_compatible

/-- The q-parameter at the corresponding bad place is nonzero. -/
theorem SourcePsiBadPlaceCompletionCorrespondence_q_nonzero
    (C : SourcePsiBadPlaceCompletionCorrespondence S v) :
    S.reduction.qParameter C.badPlace ≠ 0 :=
  S.reduction.qParameter_nonzero C.badPlace

/-- The q-parameter at the corresponding bad place is contracting. -/
theorem SourcePsiBadPlaceCompletionCorrespondence_q_contracting
    (C : SourcePsiBadPlaceCompletionCorrespondence S v) :
    ‖S.reduction.qParameter C.badPlace‖ < 1 :=
  S.reduction.qParameter_contracting C.badPlace

/-- Source multiplicative reduction corresponds to actual multiplicative
reduction under the comparison. -/
theorem SourcePsiStableReductionFromSource_actual_multiplicative_of_source
    (C : SourcePsiStableReductionComparisonData S v)
    (h : S.reduction.multiplicativeReduction C.correspondence.badPlace) :
    SourcePsiActualMultiplicativeReduction S v :=
  C.source_multiplicative_iff_actual.mp h

/-- Actual multiplicative reduction corresponds to source multiplicative
reduction under the comparison. -/
theorem SourcePsiStableReductionFromSource_source_multiplicative_of_actual
    (C : SourcePsiStableReductionComparisonData S v)
    (h : SourcePsiActualMultiplicativeReduction S v) :
    S.reduction.multiplicativeReduction C.correspondence.badPlace :=
  C.source_multiplicative_iff_actual.mpr h

/-- The comparison makes source multiplicative and actual multiplicative
reduction equivalent. -/
theorem SourcePsiStableReductionFromSource_multiplicative_iff
    (C : SourcePsiStableReductionComparisonData S v) :
    S.reduction.multiplicativeReduction C.correspondence.badPlace ↔
      SourcePsiActualMultiplicativeReduction S v :=
  C.source_multiplicative_iff_actual

/-- Actual good reduction is elliptic under the comparison. -/
theorem SourcePsiStableReductionFromSource_good_iff_elliptic
    (C : SourcePsiStableReductionComparisonData S v) :
    C.actualReduction.good ↔ (SourcePsiActualSpecialFiber S v).IsElliptic :=
  C.actualReduction.good_iff.trans
    (SourcePsiActualSpecialFiber_goodReduction_iff_isElliptic S v)

/-- Actual additive reduction is stable but not good. -/
theorem SourcePsiStableReductionFromSource_additive_not_good
    (h : SourcePsiActualAdditiveReduction S v) :
    ¬ SourcePsiActualGoodReduction S v :=
  h.not_hasGoodReduction

/-- Actual multiplicative reduction is stable but not good. -/
theorem SourcePsiStableReductionFromSource_multiplicative_not_good
    (h : SourcePsiActualMultiplicativeReduction S v) :
    ¬ SourcePsiActualGoodReduction S v :=
  h.not_hasGoodReduction

/-! ## Exact source stable-reduction boundary

Proved:
- actual stable reduction = good or multiplicative or additive, with the actual
  trichotomy;
- good/multiplicative/additive are stable; split implies multiplicative; split
  is stable;
- actual reduction type data at the completion place;
- conditional source comparison: under a supplied bad-place/completion
  correspondence and comparison data, source stable/multiplicative/split clauses
  agree with the actual reduction classes;
- source split implies source multiplicative and actual split implies actual
  multiplicative.

NOT constructed or asserted:
1. an actual bad-place/completion-place correspondence (the structure has no
   fabricated inhabitant);
2. properness/regularity of the actual minimal model;
3. component/node graph of the actual special fiber;
4. stable reduction over extensions and component/monodromy data;
5. an actual source special fiber beyond the comparison datum.

These are exact residual objects.  No stable reduction or source identification is
fabricated.
-/
end LeanFormal.IUT.SourcePsiStableReductionFromSource

end