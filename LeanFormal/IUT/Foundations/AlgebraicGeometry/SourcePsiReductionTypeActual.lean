import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiActualMinimality
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiActualMinimalModelReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Tactic

/-!
# Actual reduction types and Definition 3.1 correspondence

From an actual integral model and its actual Mathlib minimal model, this file
proves the actual good/multiplicative/additive classification and its
pairwise disjointness, defines the actual stable/split predicates, and connects
them to the Definition 3.1 reduction clause under a supplied bad-place
correspondence.  The component/node data are stated as an explicit residual
structure; no classification or component data are fabricated.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.SourcePsiReductionTypeActual

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiActualMinimalModelReduction
open LeanFormal.IUT.SourcePsiActualMinimality
open LeanFormal.IUT.SourceDefinition31Data
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- Actual minimal model of a source model at a finite place. -/
abbrev actualReductionMinimalModel
    (M : SourcePsiIntegralModelData S v) : WeierstrassCurve (SourcePsiActualField S v) :=
  correctedMinimalModel S v M

/-- Actual good reduction at the selected finite place. -/
def ActualGoodReduction (M : SourcePsiIntegralModelData S v) : Prop :=
  WeierstrassCurve.HasGoodReduction (SourcePsiActualIntegers S v)
    (actualReductionMinimalModel S v M)

/-- Actual multiplicative reduction at the selected finite place. -/
def ActualMultiplicativeReduction (M : SourcePsiIntegralModelData S v) : Prop :=
  WeierstrassCurve.HasMultiplicativeReduction (SourcePsiActualIntegers S v)
    (actualReductionMinimalModel S v M)

/-- Actual additive reduction at the selected finite place. -/
def ActualAdditiveReduction (M : SourcePsiIntegralModelData S v) : Prop :=
  WeierstrassCurve.HasAdditiveReduction (SourcePsiActualIntegers S v)
    (actualReductionMinimalModel S v M)

/-- Actual split multiplicative reduction at the selected finite place. -/
def ActualSplitMultiplicativeReduction (M : SourcePsiIntegralModelData S v) : Prop :=
  WeierstrassCurve.HasSplitMultiplicativeReduction (SourcePsiActualIntegers S v)
    (actualReductionMinimalModel S v M)

/-- Actual stable reduction = good or multiplicative. -/
def ActualStableReduction (M : SourcePsiIntegralModelData S v) : Prop :=
  ActualGoodReduction S v M ∨ ActualMultiplicativeReduction S v M

/-- Actual classification theorem, directly from Mathlib's trichotomy. -/
theorem actualReduction_trichotomy
    (M : SourcePsiIntegralModelData S v) :
    ActualGoodReduction S v M ∨
      ActualMultiplicativeReduction S v M ∨
        ActualAdditiveReduction S v M :=
  WeierstrassCurve.hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction
    (R := SourcePsiActualIntegers S v)
    (W := actualReductionMinimalModel S v M)

theorem actualGood_not_multiplicative
    (M : SourcePsiIntegralModelData S v)
    (h : ActualGoodReduction S v M) :
    ¬ ActualMultiplicativeReduction S v M :=
  WeierstrassCurve.HasGoodReduction.not_hasMultiplicativeReduction h

theorem actualGood_not_additive
    (M : SourcePsiIntegralModelData S v)
    (h : ActualGoodReduction S v M) :
    ¬ ActualAdditiveReduction S v M :=
  WeierstrassCurve.HasGoodReduction.not_hasAdditiveReduction h

theorem actualMultiplicative_not_additive
    (M : SourcePsiIntegralModelData S v)
    (h : ActualMultiplicativeReduction S v M) :
    ¬ ActualAdditiveReduction S v M :=
  WeierstrassCurve.HasMultiplicativeReduction.not_hasAdditiveReduction h

theorem actualAdditive_not_multiplicative
    (M : SourcePsiIntegralModelData S v)
    (h : ActualAdditiveReduction S v M) :
    ¬ ActualMultiplicativeReduction S v M :=
  WeierstrassCurve.HasAdditiveReduction.not_hasMultiplicativeReduction h

theorem actualSplit_multiplicative
    (M : SourcePsiIntegralModelData S v)
    (h : ActualSplitMultiplicativeReduction S v M) :
    ActualMultiplicativeReduction S v M :=
  h.toHasMultiplicativeReduction

theorem actualMultiplicative_stable
    (M : SourcePsiIntegralModelData S v)
    (h : ActualMultiplicativeReduction S v M) :
    ActualStableReduction S v M :=
  Or.inr h

theorem actualGood_stable
    (M : SourcePsiIntegralModelData S v)
    (h : ActualGoodReduction S v M) :
    ActualStableReduction S v M :=
  Or.inl h

theorem actualStable_iff_good_or_multiplicative
    (M : SourcePsiIntegralModelData S v) :
    ActualStableReduction S v M ↔
      ActualGoodReduction S v M ∨ ActualMultiplicativeReduction S v M :=
  Iff.rfl

theorem actualStable_not_additive
    (M : SourcePsiIntegralModelData S v)
    (h : ActualStableReduction S v M) :
    ¬ ActualAdditiveReduction S v M :=
  by
  rcases h with hgood | hmult
  · exact actualGood_not_additive S v M hgood
  · exact actualMultiplicative_not_additive S v M hmult

/-- Actual classification data at a place. -/
structure ActualReductionTypeData where
  good : Prop
  multiplicative : Prop
  additive : Prop
  split_multiplicative : Prop
  stable : Prop
  classification : good ∨ multiplicative ∨ additive
  split_implies_multiplicative : split_multiplicative → multiplicative
  stable_iff : stable ↔ good ∨ multiplicative

noncomputable def actualReductionTypeData
    (M : SourcePsiIntegralModelData S v) : ActualReductionTypeData where
  good := ActualGoodReduction S v M
  multiplicative := ActualMultiplicativeReduction S v M
  additive := ActualAdditiveReduction S v M
  split_multiplicative := ActualSplitMultiplicativeReduction S v M
  stable := ActualStableReduction S v M
  classification := actualReduction_trichotomy S v M
  split_implies_multiplicative := fun h => actualSplit_multiplicative S v M h
  stable_iff := actualStable_iff_good_or_multiplicative S v M

/-- A supplied bad-place correspondence: each Definition 3.1 bad place is
assigned an actual finite place and an actual source integral model there. -/
structure SourcePsiBadPlaceCorrespondence where
  placeOf : S.badPlaces → IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers S.arithmetic.F)
  coefficientsIntegral : ∀ b : S.badPlaces,
    SourcePsiCoefficientsIntegral S (placeOf b)
  modelOf : ∀ b : S.badPlaces,
    SourcePsiIntegralModelData S (placeOf b)
  modelOf_eq : ∀ b : S.badPlaces,
    modelOf b = sourcePsiIntegralModelDataOfCoefficients S (placeOf b)
      (coefficientsIntegral b)

noncomputable def sourcePsiBadPlaceModel
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) :
    SourcePsiIntegralModelData S (C.placeOf b) :=
  sourcePsiIntegralModelDataOfCoefficients S (C.placeOf b)
    (C.coefficientsIntegral b)

def SourcePsiActualGoodAt
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) : Prop :=
  ActualGoodReduction S (C.placeOf b) (sourcePsiBadPlaceModel S C b)

def SourcePsiActualMultiplicativeAt
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) : Prop :=
  ActualMultiplicativeReduction S (C.placeOf b) (sourcePsiBadPlaceModel S C b)

def SourcePsiActualAdditiveAt
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) : Prop :=
  ActualAdditiveReduction S (C.placeOf b) (sourcePsiBadPlaceModel S C b)

def SourcePsiActualSplitAt
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) : Prop :=
  ActualSplitMultiplicativeReduction S (C.placeOf b) (sourcePsiBadPlaceModel S C b)

def SourcePsiActualStableAt
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) : Prop :=
  ActualStableReduction S (C.placeOf b) (sourcePsiBadPlaceModel S C b)

theorem sourcePsiActualAt_trichotomy
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) :
    SourcePsiActualGoodAt S C b ∨
      SourcePsiActualMultiplicativeAt S C b ∨
        SourcePsiActualAdditiveAt S C b :=
  actualReduction_trichotomy S (C.placeOf b) (sourcePsiBadPlaceModel S C b)

theorem sourcePsiActualAt_split_multiplicative
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces)
    (h : SourcePsiActualSplitAt S C b) :
    SourcePsiActualMultiplicativeAt S C b :=
  actualSplit_multiplicative S (C.placeOf b) (sourcePsiBadPlaceModel S C b) h

theorem sourcePsiActualAt_multiplicative_stable
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces)
    (h : SourcePsiActualMultiplicativeAt S C b) :
    SourcePsiActualStableAt S C b :=
  actualMultiplicative_stable S (C.placeOf b) (sourcePsiBadPlaceModel S C b) h

/-- Definition 3.1 reduction-type correspondence, supplied as explicit data. -/
structure SourcePsiReductionTypeCorrespondence where
  correspondence : SourcePsiBadPlaceCorrespondence S
  stable_compat : ∀ b : S.badPlaces, SourcePsiActualStableAt S correspondence b
  multiplicative_compat : ∀ b : S.badPlaces,
    S.reduction.multiplicativeReduction b ↔
      SourcePsiActualMultiplicativeAt S correspondence b
  split_compat : ∀ b : S.badPlaces,
    S.reduction.splitMultiplicativeReduction b ↔
      SourcePsiActualSplitAt S correspondence b

theorem sourcePsiReductionType_correspondence_stable
    (D : SourcePsiReductionTypeCorrespondence S) (b : S.badPlaces) :
    S.reduction.stableReduction b ∧
      SourcePsiActualStableAt S D.correspondence b :=
  ⟨S.reduction.stableReduction_proved b, D.stable_compat b⟩

theorem sourcePsiReductionType_correspondence_multiplicative
    (D : SourcePsiReductionTypeCorrespondence S) (b : S.badPlaces) :
    S.reduction.multiplicativeReduction b ↔
      SourcePsiActualMultiplicativeAt S D.correspondence b :=
  D.multiplicative_compat b

theorem sourcePsiReductionType_correspondence_split
    (D : SourcePsiReductionTypeCorrespondence S) (b : S.badPlaces) :
    S.reduction.splitMultiplicativeReduction b ↔
      SourcePsiActualSplitAt S D.correspondence b :=
  D.split_compat b

theorem sourcePsiReductionType_correspondence_split_multiplicative
    (D : SourcePsiReductionTypeCorrespondence S) (b : S.badPlaces)
    (h : S.reduction.splitMultiplicativeReduction b) :
    S.reduction.multiplicativeReduction b :=
  S.reduction.split_implies_multiplicative b h

/-- Exact special-fiber component/node data: actual reduced curve plus a finite
component set, a finite node set and incidence.  This is residual data, not an
asserted inhabitant. -/
structure SourcePsiComponentNodeData
    (M : SourcePsiIntegralModelData S v) where
  reducedCurve : WeierstrassCurve (SourcePsiActualResidueField S v)
  reducedCurve_eq : reducedCurve = actualMinimalReduction S v M
  components : Type u
  finite_components : Fintype components
  nodes : Type u
  finite_nodes : Fintype nodes
  incidence : nodes → components × components

/-- Exact component/node residual Proposition.  No inhabitant is asserted. -/
def SourcePsiComponentNodeResidual
    (M : SourcePsiIntegralModelData S v) : Prop :=
  Nonempty (SourcePsiComponentNodeData S v M)

theorem sourcePsiComponentNodeResidual_iff
    (M : SourcePsiIntegralModelData S v) :
    SourcePsiComponentNodeResidual S v M ↔
      Nonempty (SourcePsiComponentNodeData S v M) :=
  Iff.rfl

theorem sourcePsiComponentNodeData_reducedCurve
    (M : SourcePsiIntegralModelData S v)
    (D : SourcePsiComponentNodeData S v M) :
    D.reducedCurve = actualMinimalReduction S v M :=
  D.reducedCurve_eq

theorem sourcePsiComponentNodeData_finite
    (M : SourcePsiIntegralModelData S v)
    (D : SourcePsiComponentNodeData S v M) :
    Finite D.components ∧ Finite D.nodes :=
  ⟨Finite.of_fintype D.components, Finite.of_fintype D.nodes⟩

theorem sourcePsiActualAt_stable_not_additive
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces)
    (h : SourcePsiActualStableAt S C b) :
    ¬ SourcePsiActualAdditiveAt S C b :=
  actualStable_not_additive S (C.placeOf b) (sourcePsiBadPlaceModel S C b) h

/-- Actual reduction-type data at one bad place, under the supplied
correspondence. -/
structure SourcePsiActualReductionTypeAtData
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) where
  good : Prop
  multiplicative : Prop
  additive : Prop
  split_multiplicative : Prop
  stable : Prop
  classification : good ∨ multiplicative ∨ additive
  split_implies_multiplicative : split_multiplicative → multiplicative
  stable_iff : stable ↔ good ∨ multiplicative

noncomputable def sourcePsiActualReductionTypeAtData
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) :
    SourcePsiActualReductionTypeAtData S C b where
  good := SourcePsiActualGoodAt S C b
  multiplicative := SourcePsiActualMultiplicativeAt S C b
  additive := SourcePsiActualAdditiveAt S C b
  split_multiplicative := SourcePsiActualSplitAt S C b
  stable := SourcePsiActualStableAt S C b
  classification := sourcePsiActualAt_trichotomy S C b
  split_implies_multiplicative := fun h =>
    sourcePsiActualAt_split_multiplicative S C b h
  stable_iff := Iff.rfl

theorem sourcePsiActualReductionTypeAtData_good
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) :
    (sourcePsiActualReductionTypeAtData S C b).good ↔
      SourcePsiActualGoodAt S C b :=
  Iff.rfl

theorem sourcePsiActualReductionTypeAtData_multiplicative
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) :
    (sourcePsiActualReductionTypeAtData S C b).multiplicative ↔
      SourcePsiActualMultiplicativeAt S C b :=
  Iff.rfl

theorem sourcePsiActualReductionTypeAtData_additive
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) :
    (sourcePsiActualReductionTypeAtData S C b).additive ↔
      SourcePsiActualAdditiveAt S C b :=
  Iff.rfl

theorem sourcePsiActualReductionTypeAtData_split
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) :
    (sourcePsiActualReductionTypeAtData S C b).split_multiplicative ↔
      SourcePsiActualSplitAt S C b :=
  Iff.rfl

theorem sourcePsiActualReductionTypeAtData_stable
    (C : SourcePsiBadPlaceCorrespondence S) (b : S.badPlaces) :
    (sourcePsiActualReductionTypeAtData S C b).stable ↔
      SourcePsiActualStableAt S C b :=
  Iff.rfl
end LeanFormal.IUT.SourcePsiReductionTypeActual
