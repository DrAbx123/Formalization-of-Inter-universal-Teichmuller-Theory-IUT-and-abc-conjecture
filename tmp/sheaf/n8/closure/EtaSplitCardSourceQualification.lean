import tmp.sheaf.n8.closure.EtaSourceWithBadFiniteCondition
import tmp.sheaf.n8.closure.EtaReductionRestAssemblyActual

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Second source qualification: split-multiplicative card

Adds `NativeSplitMultiplicativeCard X` as a second explicit source qualification
of the corrected Definition 3.1 target, alongside `V_mod_bad.Finite`.  This is a
source card, not an arbitrary witness: the structure field is a source target,
and the card is never constructed by the file.  The corrected target with the
two qualifications is equivalent to the first corrected target; the actual
`reductionRestRemainingOfAssembly` consumes the split card.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeReductionRestActual
open LeanFormal.IUT.N8Closure.NativeQParameterActual
open LeanFormal.IUT.N8Closure.NativeSplitMultiplicativeAttempt
open LeanFormal.IUT.N8Closure.EtaBadFiniteSourceActual
open LeanFormal.IUT.N8Closure.EtaNativeDefinition31ObjectsAssembly
open LeanFormal.IUT.N8Closure.EtaSourceWithBadFiniteCondition
open LeanFormal.IUT.N8Closure.EtaReductionRestAssemblyActual

namespace LeanFormal.IUT.N8Closure.EtaSplitCardSourceQualification

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Corrected Definition 3.1 input with the two explicit source qualifications
side by side: bad-set finiteness and the split-multiplicative card. -/
structure SourceWithTwoQualifications (X : N8NativeInput l) where
  /-- SOURCE card 1: `V_mod_bad` is finite. -/
  badFinite : RequiredBadFiniteness (X := X)
  /-- SOURCE card 2: split-multiplicative reduction at every bad lift. -/
  splitCard : NativeSplitMultiplicativeCard X
  /-- Exact remaining full-clause targets. -/
  remaining : NativeDefinition31RemainingTargets X

/-- Corrected Definition 3.1 target with both source qualifications. -/
def CorrectedDefinition31TargetWithSplit : Prop :=
  Nonempty (SourceWithTwoQualifications (l := l) X)

/-- Actual projection: source card 1 is carried explicitly. -/
theorem twoQualifications_badFinite
    (h : CorrectedDefinition31TargetWithSplit (X := X)) :
    RequiredBadFiniteness (X := X) :=
  h.some.badFinite

/-- Actual projection: source card 2 is carried explicitly. -/
theorem twoQualifications_split
    (h : CorrectedDefinition31TargetWithSplit (X := X)) :
    NativeSplitMultiplicativeTarget X :=
  h.some.splitCard.splitMultiplicativeReduction

/-- Actual conversion to the first corrected target, using the actual
`reductionRestRemainingOfAssembly` to consume the split card. -/
noncomputable def sourceQualifiedOfTwo
    (I : SourceWithTwoQualifications (X := X)) :
    SourceQualifiedDefinition31Input (X := X) where
  qualification := I.badFinite
  reductionRest := reductionRestRemainingOfAssembly X I.splitCard
  remaining := I.remaining

/-- Actual converse: the first corrected target exposes the split card through
the actual splitMultiplicativeReduction field of reduction rest. -/
noncomputable def twoOfSourceQualified
    (I : SourceQualifiedDefinition31Input (X := X)) :
    SourceWithTwoQualifications (X := X) where
  badFinite := I.qualification
  splitCard := ⟨I.reductionRest.splitMultiplicativeReduction⟩
  remaining := I.remaining

/-- Actual equivalence of the two corrected targets. -/
theorem correctedTargetWithSplit_iff_correctedTarget :
    CorrectedDefinition31TargetWithSplit (X := X) ↔
      CorrectedDefinition31Target (X := X) := by
  constructor
  · rintro ⟨I⟩
    exact ⟨sourceQualifiedOfTwo (X := X) I⟩
  · rintro ⟨I⟩
    exact ⟨twoOfSourceQualified (X := X) I⟩

/-- Actual reduction consumer: the two-qualification target yields the
SourceReductionClause using the explicit source cards. -/
noncomputable def reductionClauseOfTwoQualifications
    (I : SourceWithTwoQualifications (X := X)) :
    SourceReductionClause (NativeSelectedPlaces X) (NativeBadPlaces X) :=
  nativeReductionClauseOf X
    (nativeSourceWithBadFiniteOfSetFinite X I.badFinite)
    (reductionRestRemainingOfAssembly X I.splitCard)

/-- Both qualifications are source conditions, not constructed witnesses. -/
theorem twoQualifications_are_source_conditions
    (h : CorrectedDefinition31TargetWithSplit (X := X)) :
    RequiredBadFiniteness (X := X) ∧
      NativeSplitMultiplicativeTarget X :=
  ⟨twoQualifications_badFinite (X := X) h,
   twoQualifications_split (X := X) h⟩

end LeanFormal.IUT.N8Closure.EtaSplitCardSourceQualification

end
