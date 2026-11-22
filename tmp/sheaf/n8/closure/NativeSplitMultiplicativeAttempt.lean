import tmp.sheaf.n8.closure.NativeQParameterActual

/-!
# Native split-multiplicative attempt

What is actual:
- Clause B gives multiplicative reduction (not split) over V_mod_bad;
- the native Tate witness gives the q-candidate and the actual Wave30
  qParameter;
- if a split-multiplicative card is supplied, NativeReductionRestRemaining is
  filled actually using the Wave30 qParameter proofs.

Decisive no-go for deriving split from the current native data:
- SourceTateComparisonWitness/TateCurveComparison only supply a variable
  change realizing the local curve as a Tate q-curve; no production theorem
  transfers HasSplitMultiplicativeReductionAt from that Tate curve at a general
  number-field q-candidate to X.  The only split-reduction theorems in
  production are for the concrete p-adic canonical Tate curve (q = p) and the
  concrete five-place curve.
- HasMultiplicativeReductionAt does not imply HasSplitMultiplicativeReductionAt
  in production.
Therefore the split card cannot be derived; it is an exact missing source
declaration, not an arbitrary reduction.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeSplitMultiplicativeAttempt

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativePartitionInputsActual
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeContractFromBadFinite
open LeanFormal.IUT.N8Closure.NativeReductionRestActual
open LeanFormal.IUT.N8Closure.NativeQParameterActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- Exact split-multiplicative target at every bad place lift. -/
def NativeSplitMultiplicativeTarget (X : N8NativeInput l) : Prop :=
  ∀ b : NativeBadPlaces X,
    X.S.arithmetic.curve.HasSplitMultiplicativeReductionAt (nativeBadLift X b)

/-- Exact missing split card. -/
structure NativeSplitMultiplicativeCard (X : N8NativeInput l) where
  splitMultiplicativeReduction : NativeSplitMultiplicativeTarget X

/-- Actual equivalence between the target and the missing card. -/
theorem nativeSplitMultiplicativeTarget_iff_card
    (X : N8NativeInput l) :
    NativeSplitMultiplicativeTarget X ↔
      Nonempty (NativeSplitMultiplicativeCard X) := by
  constructor
  · intro h
    exact ⟨⟨h⟩⟩
  · rintro ⟨C⟩
    exact C.splitMultiplicativeReduction

/-- Given the exact split card, fill NativeReductionRestRemaining actually:
the qParameter and all its proofs come from Wave30, and split is the supplied
card. -/
noncomputable def nativeReductionRestRemainingOfSplit
    (X : N8NativeInput l) (C : NativeSplitMultiplicativeCard X) :
    NativeReductionRestRemaining X where
  splitMultiplicativeReduction := C.splitMultiplicativeReduction
  qParameter := nativeQParameter X
  qParameter_nonzero := nativeQParameter_ne_zero X
  qParameter_contracting := nativeQParameter_contracting X
  qParameter_reduction_compatibility :=
    nativeQParameter_reduction_compatibility X

/-- The only missing data for the full reduction rest is the split card; with
it the remaining structure is actual. -/
theorem nativeReductionRestRemaining_of_split_nonempty
    (X : N8NativeInput l) (C : NativeSplitMultiplicativeCard X) :
    Nonempty (NativeReductionRestRemaining X) :=
  ⟨nativeReductionRestRemainingOfSplit X C⟩

end LeanFormal.IUT.N8Closure.NativeSplitMultiplicativeAttempt
