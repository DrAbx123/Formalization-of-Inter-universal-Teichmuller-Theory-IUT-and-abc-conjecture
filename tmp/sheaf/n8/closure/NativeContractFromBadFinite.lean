import tmp.sheaf.n8.closure.NativeBadFiniteTargetCorrection

/-!
# Native contract from bad finite

Using the corrected NativeSourceWithBadFinite and its actual partition, this
file constructs the next actual contract piece: SourceReductionClause from the
explicit remaining reduction data.

Actual:
- nativeSourceWithBadFinitePartitionInputs / partition (from Wave27);
- NativeReductionRest: exact remaining reduction/q fields;
- nativeReductionOfBadFinite: actual SourceReductionClause from corrected
  input plus NativeReductionRest.

Still missing (exact blockers, no production constructors):
- torsion: NativeTorsionTarget l;
- orbicurve: NativeOrbicurveTarget;
- sections: NativeSectionsTarget;
- cusp: NativeCuspTarget;
- five arithmetic compatibility slots: NativeArithmeticCompatibilityTarget.

No arbitrary record is supplied.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeContractFromBadFinite

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativePartitionInputsActual
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- Exact remaining data for SourceReductionClause after the actual corrected
partition is supplied. -/
structure NativeReductionRest (X : N8NativeInput l) where
  stableReduction : NativeBadPlaces X → Prop
  stableReduction_proved : ∀ b, stableReduction b
  multiplicativeReduction : NativeBadPlaces X → Prop
  multiplicativeReduction_proved : ∀ b, multiplicativeReduction b
  splitMultiplicativeReduction : NativeBadPlaces X → Prop
  splitMultiplicativeReduction_proved : ∀ b, splitMultiplicativeReduction b
  reductionCompatibility : ∀ b,
    splitMultiplicativeReduction b → multiplicativeReduction b
  qParameter : NativeBadPlaces X → Real
  qParameter_nonzero : ∀ b, qParameter b ≠ 0
  qParameter_contracting : ∀ b, ‖qParameter b‖ < 1
  qParameter_reduction_compatibility : ∀ b,
    stableReduction b → qParameter b ≠ 1

/-- Actual SourceReductionClause from the corrected bad-finite input and the
explicit remaining data. -/
noncomputable def nativeReductionOfBadFinite
    (X : N8NativeInput l) (C : NativeSourceWithBadFinite X)
    (R : NativeReductionRest X) :
    SourceReductionClause (NativeSelectedPlaces X) (NativeBadPlaces X) :=
  nativeReductionOfInputs X {
    partition := nativeSourceWithBadFinitePartitionInputs X C
    stableReduction := R.stableReduction
    stableReduction_proved := R.stableReduction_proved
    multiplicativeReduction := R.multiplicativeReduction
    multiplicativeReduction_proved := R.multiplicativeReduction_proved
    splitMultiplicativeReduction := R.splitMultiplicativeReduction
    splitMultiplicativeReduction_proved :=
      R.splitMultiplicativeReduction_proved
    reductionCompatibility := R.reductionCompatibility
    qParameter := R.qParameter
    qParameter_nonzero := R.qParameter_nonzero
    qParameter_contracting := R.qParameter_contracting
    qParameter_reduction_compatibility :=
      R.qParameter_reduction_compatibility }

/-- Actual partition produced by the corrected input (consumer-facing name). -/
noncomputable def nativePartitionOfBadFinite
    (X : N8NativeInput l) (C : NativeSourceWithBadFinite X) :
    SourcePlacePartition (NativeSelectedPlaces X) (NativeBadPlaces X) :=
  nativeSourceWithBadFinitePartition X C

/-- Exact remaining contract blocker package.  The four clause targets and the
compatibility target are not constructed; no arbitrary record fills them. -/
structure NativeRemainingContractBlockers (X : N8NativeInput l) where
  reductionRest : NativeReductionRest X
  torsion : NativeTorsionTarget l
  orbicurve : NativeOrbicurveTarget
  sections : NativeSectionsTarget
  cusp : NativeCuspTarget
  arithmeticCompatibility : NativeArithmeticCompatibilityTarget

end LeanFormal.IUT.N8Closure.NativeContractFromBadFinite
