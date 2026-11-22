/-
  Consumer package for the final stable-reduction comparison.

  This file separates the unconditional actual reduction-type data and the
  unconditional Definition 3.1 source reduction data from the conditional
  bad-place/completion correspondence data.  The actual package is inhabited by
  Mathlib's reduction classes; the source package is inhabited by Definition 3.1.
  The correspondence package has no fabricated inhabitant and records the exact
  stable/multiplicative/split comparison fields.

  No stable reduction, source identification, or component is invented.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiStableReductionFinal

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiStableReductionFinalConsumer

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiReductionSpecialFiber
open LeanFormal.IUT.SourcePsiActualSpecialFiber
open LeanFormal.IUT.SourcePsiActualMinimalSpecialFiber
open LeanFormal.IUT.SourcePsiSourceSpecialFiberComparison
open LeanFormal.IUT.SourcePsiStableReductionFromSource
open LeanFormal.IUT.SourcePsiStableReductionFinal
open LeanFormal.IUT.SourcePsiResidueRingFinite
open LeanFormal.IUT.AdicCompletionFractionField
open LeanFormal.IUT.SourcePsiMinimalModelCriterion
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- Unconditional actual reduction-type consumer data.  This is Mathlib's actual
good/multiplicative/additive/split data for the actual minimal reduction. -/
structure SourcePsiActualReductionTypeConsumerData where
  good : Prop
  multiplicative : Prop
  additive : Prop
  splitMultiplicative : Prop
  good_iff : good ↔ SourcePsiActualGoodReduction S v
  multiplicative_iff : multiplicative ↔ SourcePsiActualMultiplicativeReduction S v
  additive_iff : additive ↔ SourcePsiActualAdditiveReduction S v
  split_iff : splitMultiplicative ↔ SourcePsiActualSplitMultiplicativeReduction S v
  good_iff_elliptic :
    good ↔ (SourcePsiActualSpecialFiber S v).IsElliptic
  stable_trichotomy : good ∨ multiplicative ∨ additive
  split_imp_multiplicative : splitMultiplicative → multiplicative
  multiplicative_not_good : multiplicative → ¬ good
  additive_not_good : additive → ¬ good

/-- The actual reduction-type consumer data, inhabited from Mathlib's classes. -/
def sourcePsiActualReductionTypeConsumerData :
    SourcePsiActualReductionTypeConsumerData S v where
  good := SourcePsiActualGoodReduction S v
  multiplicative := SourcePsiActualMultiplicativeReduction S v
  additive := SourcePsiActualAdditiveReduction S v
  splitMultiplicative := SourcePsiActualSplitMultiplicativeReduction S v
  good_iff := Iff.rfl
  multiplicative_iff := Iff.rfl
  additive_iff := Iff.rfl
  split_iff := Iff.rfl
  good_iff_elliptic :=
    SourcePsiActualSpecialFiber_goodReduction_iff_isElliptic S v
  stable_trichotomy :=
    SourcePsiActualSpecialFiber_reduction_trichotomy S v
  split_imp_multiplicative :=
    fun h => SourcePsiActualSplit_imp_multiplicative S v h
  multiplicative_not_good :=
    fun h => h.not_hasGoodReduction
  additive_not_good :=
    fun h => h.not_hasGoodReduction

/-- Consumer form: actual stable trichotomy. -/
theorem SourcePsiActualReductionTypeConsumer_trichotomy :
    (sourcePsiActualReductionTypeConsumerData S v).good ∨
      (sourcePsiActualReductionTypeConsumerData S v).multiplicative ∨
        (sourcePsiActualReductionTypeConsumerData S v).additive :=
  (sourcePsiActualReductionTypeConsumerData S v).stable_trichotomy

/-- Consumer form: actual good iff elliptic. -/
theorem SourcePsiActualReductionTypeConsumer_good_iff_elliptic :
    (sourcePsiActualReductionTypeConsumerData S v).good ↔
      (SourcePsiActualSpecialFiber S v).IsElliptic :=
  (sourcePsiActualReductionTypeConsumerData S v).good_iff_elliptic

/-- Consumer form: actual split implies multiplicative. -/
theorem SourcePsiActualReductionTypeConsumer_split_imp_multiplicative :
    (sourcePsiActualReductionTypeConsumerData S v).splitMultiplicative →
      (sourcePsiActualReductionTypeConsumerData S v).multiplicative :=
  (sourcePsiActualReductionTypeConsumerData S v).split_imp_multiplicative

/-- Unconditional Definition 3.1 source reduction consumer data at a bad
place. -/
structure SourcePsiDefinition31ReductionConsumerData (b : S.badPlaces) where
  stable : SourcePsiDefinition31StableReduction S b
  multiplicative : SourcePsiDefinition31MultiplicativeReduction S b
  splitMultiplicative : SourcePsiDefinition31SplitMultiplicativeReduction S b
  split_imp_multiplicative :
    SourcePsiDefinition31SplitMultiplicativeReduction S b →
      SourcePsiDefinition31MultiplicativeReduction S b
  q_nonzero : S.reduction.qParameter b ≠ 0
  q_contracting : ‖S.reduction.qParameter b‖ < 1

/-- The Definition 3.1 source reduction data at every bad place. -/
def sourcePsiDefinition31ReductionConsumerData (b : S.badPlaces) :
    SourcePsiDefinition31ReductionConsumerData S b where
  stable := SourcePsiDefinition31StableReduction_proved S b
  multiplicative := SourcePsiDefinition31MultiplicativeReduction_proved S b
  splitMultiplicative := SourcePsiDefinition31SplitMultiplicativeReduction_proved S b
  split_imp_multiplicative :=
    fun h => S.reduction.reductionCompatibility b h
  q_nonzero := S.reduction.qParameter_nonzero b
  q_contracting := S.reduction.qParameter_contracting b

/-- Consumer form: source stable clause. -/
theorem SourcePsiDefinition31ReductionConsumer_stable
    (b : S.badPlaces) :
    (sourcePsiDefinition31ReductionConsumerData S b).stable :=
  (sourcePsiDefinition31ReductionConsumerData S b).stable

/-- Consumer form: source split implies multiplicative. -/
theorem SourcePsiDefinition31ReductionConsumer_split_imp_multiplicative
    (b : S.badPlaces) :
    (sourcePsiDefinition31ReductionConsumerData S b).splitMultiplicative →
      (sourcePsiDefinition31ReductionConsumerData S b).multiplicative :=
  (sourcePsiDefinition31ReductionConsumerData S b).split_imp_multiplicative

/-- Conditional correspondence consumer data: exact bad-place/completion
correspondence plus source/actual packages and the three comparison fields. -/
structure SourcePsiStableReductionCorrespondenceConsumerData where
  final : SourcePsiStableReductionFinalData S v
  source : SourcePsiDefinition31ReductionConsumerData S final.correspondence.badPlace
  actual : SourcePsiActualReductionTypeConsumerData S v
  stable_iff :
    S.reduction.stableReduction final.correspondence.badPlace ↔
      SourcePsiActualStableReduction S v
  multiplicative_iff :
    S.reduction.multiplicativeReduction final.correspondence.badPlace ↔
      SourcePsiActualMultiplicativeReduction S v
  split_iff :
    S.reduction.splitMultiplicativeReduction final.correspondence.badPlace ↔
      SourcePsiActualSplitMultiplicativeReduction S v

/-- A final stable-reduction datum yields the correspondence consumer data. -/
def sourcePsiStableReductionCorrespondenceConsumerData
    (D : SourcePsiStableReductionFinalData S v) :
    SourcePsiStableReductionCorrespondenceConsumerData S v where
  final := D
  source := sourcePsiDefinition31ReductionConsumerData S D.correspondence.badPlace
  actual := sourcePsiActualReductionTypeConsumerData S v
  stable_iff := D.source_stable_iff_actual
  multiplicative_iff := D.source_multiplicative_iff_actual
  split_iff := D.source_split_iff_actual

/-- Consumer form: stable comparison under the correspondence. -/
theorem SourcePsiStableReductionCorrespondence_stable_iff
    (C : SourcePsiStableReductionCorrespondenceConsumerData S v) :
    S.reduction.stableReduction C.final.correspondence.badPlace ↔
      SourcePsiActualStableReduction S v :=
  C.stable_iff

/-- Consumer form: multiplicative comparison under the correspondence. -/
theorem SourcePsiStableReductionCorrespondence_multiplicative_iff
    (C : SourcePsiStableReductionCorrespondenceConsumerData S v) :
    S.reduction.multiplicativeReduction C.final.correspondence.badPlace ↔
      SourcePsiActualMultiplicativeReduction S v :=
  C.multiplicative_iff

/-- Consumer form: split comparison under the correspondence. -/
theorem SourcePsiStableReductionCorrespondence_split_iff
    (C : SourcePsiStableReductionCorrespondenceConsumerData S v) :
    S.reduction.splitMultiplicativeReduction C.final.correspondence.badPlace ↔
      SourcePsiActualSplitMultiplicativeReduction S v :=
  C.split_iff

/-- Consumer form: source split reduction at the corresponding bad place. -/
theorem SourcePsiStableReductionCorrespondence_source_split
    (C : SourcePsiStableReductionCorrespondenceConsumerData S v) :
    S.reduction.splitMultiplicativeReduction C.final.correspondence.badPlace :=
  C.source.splitMultiplicative

/-- Consumer form: actual split reduction from the correspondence. -/
theorem SourcePsiStableReductionCorrespondence_actual_split
    (C : SourcePsiStableReductionCorrespondenceConsumerData S v) :
    SourcePsiActualSplitMultiplicativeReduction S v :=
  C.split_iff.mp (SourcePsiStableReductionCorrespondence_source_split S v C)

/-- Consumer form: actual stable trichotomy from the correspondence package. -/
theorem SourcePsiStableReductionCorrespondence_actual_trichotomy
    (C : SourcePsiStableReductionCorrespondenceConsumerData S v) :
    C.actual.good ∨ C.actual.multiplicative ∨ C.actual.additive :=
  C.actual.stable_trichotomy

/-- Exact correspondence consumer residual: the correspondence package and its
comparison fields.  No inhabitant is asserted. -/
def SourcePsiStableReductionFinalConsumerResidual : Prop :=
  (∃ C : SourcePsiStableReductionCorrespondenceConsumerData S v,
    S.reduction.stableReduction C.final.correspondence.badPlace ↔
      SourcePsiActualStableReduction S v) ∧
    (∃ b : S.badPlaces,
      Nonempty (SourcePsiDefinition31ReductionConsumerData S b))



/-- Consumer form: actual good reduction iff elliptic. -/
theorem SourcePsiActualReductionTypeConsumer_good_iff_elliptic'
    (C : SourcePsiActualReductionTypeConsumerData S v) :
    C.good ↔ (SourcePsiActualSpecialFiber S v).IsElliptic :=
  C.good_iff_elliptic

/-- Consumer form: actual multiplicative reduction is not good. -/
theorem SourcePsiActualReductionTypeConsumer_multiplicative_not_good
    (C : SourcePsiActualReductionTypeConsumerData S v) :
    C.multiplicative → ¬ C.good :=
  C.multiplicative_not_good

/-- Consumer form: actual additive reduction is not good. -/
theorem SourcePsiActualReductionTypeConsumer_additive_not_good
    (C : SourcePsiActualReductionTypeConsumerData S v) :
    C.additive → ¬ C.good :=
  C.additive_not_good

/-! ## Exact final consumer boundary

Unconditional packages:
- actual good/multiplicative/additive/split reduction data, actual trichotomy,
  good iff elliptic, split implies multiplicative, mult/additive not good;
- Definition 3.1 stable/multiplicative/split clauses at every bad place, with
  split implies multiplicative and q-parameter nonzero/contracting.

Conditional package:
- exact bad-place/completion correspondence plus source and actual packages;
- stable, multiplicative, and split comparison fields;
- actual split and actual trichotomy consumers.

NOT constructed or asserted:
- the bad-place/completion-place correspondence;
- the comparison iff fields;
- properness/regularity of the actual minimal model;
- component/node data;
- stable reduction over extensions/monodromy;
- an actual source special fiber beyond the comparison datum.

No stable reduction, component, or source object is fabricated.
-/
end LeanFormal.IUT.SourcePsiStableReductionFinalConsumer

end