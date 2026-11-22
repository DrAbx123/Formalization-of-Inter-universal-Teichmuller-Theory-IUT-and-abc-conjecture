/-
  Final stable/multiplicative/split comparison from Definition 3.1 and the actual
  Mathlib reduction.

  The actual minimal reduction supplies the good/multiplicative/additive
  trichotomy.  Definition 3.1 supplies stable, multiplicative and split
  multiplicative clauses at bad places, with the split-implies-multiplicative
  compatibility.  Under a precise bad-place/completion-place correspondence and
  comparison data, this file proves the stable, multiplicative and split
  comparisons, the actual trichotomy, and the split/multiplicative chains.

  The correspondence and the proper/regular/component data are stated as exact
  residual hypotheses; no stable reduction, component, or source object is
  fabricated.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiStableReductionFromSource

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiStableReductionFinal

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiReductionSpecialFiber
open LeanFormal.IUT.SourcePsiActualSpecialFiber
open LeanFormal.IUT.SourcePsiActualMinimalSpecialFiber
open LeanFormal.IUT.SourcePsiSourceSpecialFiberComparison
open LeanFormal.IUT.SourcePsiStableReductionFromSource
open LeanFormal.IUT.SourcePsiResidueRingFinite
open LeanFormal.IUT.AdicCompletionFractionField
open LeanFormal.IUT.SourcePsiMinimalModelCriterion
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- Final stable-reduction comparison datum.  The structure packages the exact
bad-place/completion correspondence, Definition 3.1 reduction data, actual
reduction data, and the three source/actual comparison fields.  No inhabitant is
asserted. -/
structure SourcePsiStableReductionFinalData where
  correspondence : SourcePsiBadPlaceCompletionCorrespondence S v
  sourceReduction : SourcePsiDefinition31ReductionTypeData S correspondence.badPlace
  actualReduction : SourcePsiActualReductionTypeAtCompletion S v
  source_stable_iff_actual :
    S.reduction.stableReduction correspondence.badPlace ↔
      SourcePsiActualStableReduction S v
  source_multiplicative_iff_actual :
    S.reduction.multiplicativeReduction correspondence.badPlace ↔
      SourcePsiActualMultiplicativeReduction S v
  source_split_iff_actual :
    S.reduction.splitMultiplicativeReduction correspondence.badPlace ↔
      SourcePsiActualSplitMultiplicativeReduction S v

/-- Source stable reduction comparison: source stable iff actual stable. -/
theorem SourcePsiStableReductionFinal_stable_iff
    (D : SourcePsiStableReductionFinalData S v) :
    S.reduction.stableReduction D.correspondence.badPlace ↔
      SourcePsiActualStableReduction S v :=
  D.source_stable_iff_actual

/-- Source multiplicative comparison. -/
theorem SourcePsiStableReductionFinal_multiplicative_iff
    (D : SourcePsiStableReductionFinalData S v) :
    S.reduction.multiplicativeReduction D.correspondence.badPlace ↔
      SourcePsiActualMultiplicativeReduction S v :=
  D.source_multiplicative_iff_actual

/-- Source split multiplicative comparison. -/
theorem SourcePsiStableReductionFinal_split_iff
    (D : SourcePsiStableReductionFinalData S v) :
    S.reduction.splitMultiplicativeReduction D.correspondence.badPlace ↔
      SourcePsiActualSplitMultiplicativeReduction S v :=
  D.source_split_iff_actual

/-- Source stable clause gives actual stable reduction. -/
theorem SourcePsiStableReductionFinal_actual_stable_of_source
    (D : SourcePsiStableReductionFinalData S v) :
    SourcePsiActualStableReduction S v :=
  D.source_stable_iff_actual.mp
    (S.reduction.stableReduction_proved D.correspondence.badPlace)

/-- Actual stable reduction gives the source stable clause. -/
theorem SourcePsiStableReductionFinal_source_stable_of_actual
    (D : SourcePsiStableReductionFinalData S v)
    (h : SourcePsiActualStableReduction S v) :
    S.reduction.stableReduction D.correspondence.badPlace :=
  D.source_stable_iff_actual.mpr h

/-- Source split multiplicative reduction gives actual split multiplicative
reduction. -/
theorem SourcePsiStableReductionFinal_actual_split_of_source
    (D : SourcePsiStableReductionFinalData S v) :
    SourcePsiActualSplitMultiplicativeReduction S v :=
  D.source_split_iff_actual.mp
    (S.reduction.splitMultiplicativeReduction_proved D.correspondence.badPlace)

/-- Actual split multiplicative reduction gives the source split clause. -/
theorem SourcePsiStableReductionFinal_source_split_of_actual
    (D : SourcePsiStableReductionFinalData S v)
    (h : SourcePsiActualSplitMultiplicativeReduction S v) :
    S.reduction.splitMultiplicativeReduction D.correspondence.badPlace :=
  D.source_split_iff_actual.mpr h

/-- Source split implies source multiplicative at the corresponding bad place. -/
theorem SourcePsiStableReductionFinal_source_split_imp_multiplicative
    (D : SourcePsiStableReductionFinalData S v) :
    S.reduction.splitMultiplicativeReduction D.correspondence.badPlace →
      S.reduction.multiplicativeReduction D.correspondence.badPlace :=
  fun h => S.reduction.reductionCompatibility D.correspondence.badPlace h

/-- Actual split implies actual multiplicative. -/
theorem SourcePsiStableReductionFinal_actual_split_imp_multiplicative
    (D : SourcePsiStableReductionFinalData S v) :
    SourcePsiActualSplitMultiplicativeReduction S v →
      SourcePsiActualMultiplicativeReduction S v :=
  fun h => SourcePsiActualSplit_imp_multiplicative S v h

/-- Actual stable trichotomy. -/
theorem SourcePsiStableReductionFinal_actual_trichotomy
    (D : SourcePsiStableReductionFinalData S v) :
    SourcePsiActualGoodReduction S v ∨
      SourcePsiActualMultiplicativeReduction S v ∨
        SourcePsiActualAdditiveReduction S v :=
  D.actualReduction.stable_trichotomy

/-- Exact final comparison theorem: stable, multiplicative and split clauses
agree with the actual classes, and the actual trichotomy and split/multiplicative
chains hold. -/
theorem SourcePsiStableReductionFinal_comparison
    (D : SourcePsiStableReductionFinalData S v) :
    (S.reduction.stableReduction D.correspondence.badPlace ↔
        SourcePsiActualStableReduction S v) ∧
      (S.reduction.multiplicativeReduction D.correspondence.badPlace ↔
        SourcePsiActualMultiplicativeReduction S v) ∧
        (S.reduction.splitMultiplicativeReduction D.correspondence.badPlace ↔
          SourcePsiActualSplitMultiplicativeReduction S v) ∧
          (SourcePsiActualGoodReduction S v ∨
            SourcePsiActualMultiplicativeReduction S v ∨
              SourcePsiActualAdditiveReduction S v) ∧
            (SourcePsiActualSplitMultiplicativeReduction S v →
              SourcePsiActualMultiplicativeReduction S v) ∧
              (S.reduction.splitMultiplicativeReduction D.correspondence.badPlace →
                S.reduction.multiplicativeReduction D.correspondence.badPlace) :=
  ⟨D.source_stable_iff_actual,
    D.source_multiplicative_iff_actual,
    D.source_split_iff_actual,
    D.actualReduction.stable_trichotomy,
    fun h => SourcePsiActualSplit_imp_multiplicative S v h,
    fun h => S.reduction.reductionCompatibility D.correspondence.badPlace h⟩

/-- Exact final residual: a correspondence/comparison datum and the missing
proper/regular/component/stable geometric data.  No inhabitant is asserted. -/
def SourcePsiStableReductionFinalResidual : Prop :=
  (∃ D : SourcePsiStableReductionFinalData S v,
    S.reduction.stableReduction D.correspondence.badPlace ↔
      SourcePsiActualStableReduction S v) ∧
    (∃ b : S.badPlaces, Nonempty (SourcePsiDefinition31ReductionTypeData S b))

/-- Exact final stable-reduction statement under a supplied final datum. -/
def SourcePsiStableReductionFinalStatement
    (D : SourcePsiStableReductionFinalData S v) : Prop :=
  (S.reduction.stableReduction D.correspondence.badPlace ↔
      SourcePsiActualStableReduction S v) ∧
    (S.reduction.multiplicativeReduction D.correspondence.badPlace ↔
      SourcePsiActualMultiplicativeReduction S v) ∧
      (S.reduction.splitMultiplicativeReduction D.correspondence.badPlace ↔
        SourcePsiActualSplitMultiplicativeReduction S v) ∧
        (SourcePsiActualGoodReduction S v ∨
          SourcePsiActualMultiplicativeReduction S v ∨
            SourcePsiActualAdditiveReduction S v)

/-- The final statement is exactly the comparison fields. -/
theorem SourcePsiStableReductionFinalStatement_iff
    (D : SourcePsiStableReductionFinalData S v) :
    SourcePsiStableReductionFinalStatement S v D :=
  ⟨D.source_stable_iff_actual,
    D.source_multiplicative_iff_actual,
    D.source_split_iff_actual,
    D.actualReduction.stable_trichotomy⟩



/-- The corresponding bad place has nonzero q-parameter. -/
theorem SourcePsiStableReductionFinal_q_nonzero
    (D : SourcePsiStableReductionFinalData S v) :
    S.reduction.qParameter D.correspondence.badPlace ≠ 0 :=
  S.reduction.qParameter_nonzero D.correspondence.badPlace

/-- The corresponding bad place has contracting q-parameter. -/
theorem SourcePsiStableReductionFinal_q_contracting
    (D : SourcePsiStableReductionFinalData S v) :
    ‖S.reduction.qParameter D.correspondence.badPlace‖ < 1 :=
  S.reduction.qParameter_contracting D.correspondence.badPlace

/-- Source split multiplicative reduction gives source multiplicative reduction. -/
theorem SourcePsiStableReductionFinal_source_multiplicative_of_split
    (D : SourcePsiStableReductionFinalData S v) :
    S.reduction.multiplicativeReduction D.correspondence.badPlace :=
  S.reduction.reductionCompatibility D.correspondence.badPlace
    (S.reduction.splitMultiplicativeReduction_proved D.correspondence.badPlace)

/-- Source split multiplicative reduction gives actual multiplicative and stable
reduction. -/
theorem SourcePsiStableReductionFinal_actual_multiplicative_and_stable_of_source_split
    (D : SourcePsiStableReductionFinalData S v) :
    SourcePsiActualMultiplicativeReduction S v ∧
      SourcePsiActualStableReduction S v :=
  ⟨D.source_multiplicative_iff_actual.mp
      (SourcePsiStableReductionFinal_source_multiplicative_of_split S v D),
    SourcePsiActualStableReduction_of_multiplicative S v
      (D.source_multiplicative_iff_actual.mp
        (SourcePsiStableReductionFinal_source_multiplicative_of_split S v D))⟩

/-- Actual good reduction is exactly ellipticity of the actual special fiber. -/
theorem SourcePsiStableReductionFinal_good_iff_elliptic
    (D : SourcePsiStableReductionFinalData S v) :
    SourcePsiActualGoodReduction S v ↔
      (SourcePsiActualSpecialFiber S v).IsElliptic :=
  SourcePsiActualSpecialFiber_goodReduction_iff_isElliptic S v

/-- Actual multiplicative reduction is not good. -/
theorem SourcePsiStableReductionFinal_multiplicative_not_good
    (D : SourcePsiStableReductionFinalData S v)
    (h : SourcePsiActualMultiplicativeReduction S v) :
    ¬ SourcePsiActualGoodReduction S v :=
  h.not_hasGoodReduction

/-- Actual additive reduction is not good. -/
theorem SourcePsiStableReductionFinal_additive_not_good
    (D : SourcePsiStableReductionFinalData S v)
    (h : SourcePsiActualAdditiveReduction S v) :
    ¬ SourcePsiActualGoodReduction S v :=
  h.not_hasGoodReduction

/-- Actual stable reduction is equivalently the good/multiplicative/additive
trichotomy. -/
theorem SourcePsiStableReductionFinal_stable_iff_trichotomy
    (D : SourcePsiStableReductionFinalData S v) :
    SourcePsiActualStableReduction S v ↔
      (SourcePsiActualGoodReduction S v ∨
        SourcePsiActualMultiplicativeReduction S v ∨
          SourcePsiActualAdditiveReduction S v) :=
  Iff.rfl

/-- The correspondence projection: the source selected place is the included
bad place. -/
theorem SourcePsiStableReductionFinal_place_compatible
    (D : SourcePsiStableReductionFinalData S v) :
    D.correspondence.comparison.place =
      S.reduction.partition.badIncluded D.correspondence.badPlace :=
  D.correspondence.place_compatible

/-- All final comparison fields in one consumer conjunction. -/
theorem SourcePsiStableReductionFinal_all_fields
    (D : SourcePsiStableReductionFinalData S v) :
    (S.reduction.stableReduction D.correspondence.badPlace ↔
        SourcePsiActualStableReduction S v) ∧
      (S.reduction.multiplicativeReduction D.correspondence.badPlace ↔
        SourcePsiActualMultiplicativeReduction S v) ∧
        (S.reduction.splitMultiplicativeReduction D.correspondence.badPlace ↔
          SourcePsiActualSplitMultiplicativeReduction S v) ∧
          (SourcePsiActualGoodReduction S v ↔
            (SourcePsiActualSpecialFiber S v).IsElliptic) ∧
            (SourcePsiActualGoodReduction S v ∨
              SourcePsiActualMultiplicativeReduction S v ∨
                SourcePsiActualAdditiveReduction S v) :=
  ⟨D.source_stable_iff_actual,
    D.source_multiplicative_iff_actual,
    D.source_split_iff_actual,
    SourcePsiStableReductionFinal_good_iff_elliptic S v D,
    D.actualReduction.stable_trichotomy⟩

/-! ## Exact final boundary

Proved under a supplied final datum:
- source stable reduction iff actual stable reduction;
- source multiplicative iff actual multiplicative;
- source split multiplicative iff actual split multiplicative;
- source split implies source multiplicative;
- actual split implies actual multiplicative;
- actual good/multiplicative/additive trichotomy;
- source split and source stable clauses are Definition 3.1 data.

NOT constructed or asserted:
1. the bad-place/completion-place correspondence;
2. the source/actual comparison iff fields;
3. properness/regularity of the actual minimal model;
4. component/node graph of the actual special fiber;
5. stable reduction over extensions and monodromy/component action;
6. an actual source special fiber or source identification.

These are exact residual objects.  No stable reduction, component, or source object
is fabricated.
-/
end LeanFormal.IUT.SourcePsiStableReductionFinal

end