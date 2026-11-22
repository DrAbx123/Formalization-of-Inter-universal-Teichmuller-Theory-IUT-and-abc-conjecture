import tmp.sheaf.n8.closure.NativeContractFromBadFinite

/-!
# Native reduction rest actual attempt

Actual from native clauses A/B:
- nativeBadLift: choose a finite F-place above each bad Fmod-place using
  NumberFieldFinitePlace.comap_surjective;
- nativeBadStableReduction: Clause A stable reduction at that lift;
- nativeBadMultiplicativeReduction: Clause B multiplicative reduction over
  V_mod_bad at that lift;
- NativeReductionStableMultiplicative packages these actual fields.

Still missing: the split-multiplicative reduction card, a real qParameter
bridge from the native completion q, and its nonzero/contracting/q != 1
proofs.  Clause B supplies multiplicative (not split) reduction and a Tate
comparison witness whose q lives in the local completion, not a real
qParameter.  These are exact source gaps; no arbitrary reduction is supplied.

Given the remaining fields, the full NativeReductionRest is constructed
actually (reductionCompatibility follows from split => multiplicative).
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeReductionRestActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativePartitionInputsActual
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeContractFromBadFinite
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- Choose a finite F-place above a bad Fmod-place. -/
noncomputable def nativeBadLift (X : N8NativeInput l) (b : NativeBadPlaces X) :
    NumberField.FinitePlace X.S.arithmetic.F :=
  (NumberFieldFinitePlace.comap_surjective
    (k := X.S.arithmetic.Fmod) (K := X.S.arithmetic.F) b.1).choose

/-- The chosen lift restricts to the bad Fmod-place. -/
theorem nativeBadLift_comap (X : N8NativeInput l) (b : NativeBadPlaces X) :
    NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod)
      (nativeBadLift X b) = b.1 :=
  (NumberFieldFinitePlace.comap_surjective
    (k := X.S.arithmetic.Fmod) (K := X.S.arithmetic.F) b.1).choose_spec

/-- Actual stable reduction at every bad place, from Clause A. -/
theorem nativeBadStableReduction (X : N8NativeInput l)
    (b : NativeBadPlaces X) :
    X.S.arithmetic.curve.HasStableReductionAt (nativeBadLift X b) :=
  X.S.clauseA.stable_reduction_nonarchimedean (nativeBadLift X b)

/-- Actual multiplicative reduction at every bad place, from Clause B. -/
theorem nativeBadMultiplicativeReduction (X : N8NativeInput l)
    (b : NativeBadPlaces X) :
    X.S.arithmetic.curve.HasMultiplicativeReductionAt (nativeBadLift X b) :=
  X.S.clauseB.multiplicative_over_bad (nativeBadLift X b) (by
    rw [nativeBadLift_comap]
    exact b.2)

/-- Actual stable+multiplicative partial reduction data. -/
structure NativeReductionStableMultiplicative (X : N8NativeInput l) where
  stableReduction : NativeBadPlaces X → Prop
  stableReduction_proved : ∀ b, stableReduction b
  multiplicativeReduction : NativeBadPlaces X → Prop
  multiplicativeReduction_proved : ∀ b, multiplicativeReduction b

/-- Actual partial data from clauses A/B. -/
noncomputable def nativeReductionStableMultiplicative
    (X : N8NativeInput l) : NativeReductionStableMultiplicative X where
  stableReduction := fun b =>
    X.S.arithmetic.curve.HasStableReductionAt (nativeBadLift X b)
  stableReduction_proved := nativeBadStableReduction X
  multiplicativeReduction := fun b =>
    X.S.arithmetic.curve.HasMultiplicativeReductionAt (nativeBadLift X b)
  multiplicativeReduction_proved := nativeBadMultiplicativeReduction X

/-- Exact remaining reduction fields not supplied by native data. -/
structure NativeReductionRestRemaining (X : N8NativeInput l) where
  splitMultiplicativeReduction : ∀ b : NativeBadPlaces X,
    X.S.arithmetic.curve.HasSplitMultiplicativeReductionAt (nativeBadLift X b)
  qParameter : NativeBadPlaces X → Real
  qParameter_nonzero : ∀ b, qParameter b ≠ 0
  qParameter_contracting : ∀ b, ‖qParameter b‖ < 1
  qParameter_reduction_compatibility : ∀ b,
    X.S.arithmetic.curve.HasStableReductionAt (nativeBadLift X b) →
      qParameter b ≠ 1

/-- Full NativeReductionRest from the actual A/B partial data plus the exact
remaining fields.  reductionCompatibility is derived from split =>
multiplicative. -/
noncomputable def nativeReductionRestOfRemaining
    (X : N8NativeInput l) (R : NativeReductionRestRemaining X) :
    NativeReductionRest X where
  stableReduction := fun b =>
    X.S.arithmetic.curve.HasStableReductionAt (nativeBadLift X b)
  stableReduction_proved := nativeBadStableReduction X
  multiplicativeReduction := fun b =>
    X.S.arithmetic.curve.HasMultiplicativeReductionAt (nativeBadLift X b)
  multiplicativeReduction_proved := nativeBadMultiplicativeReduction X
  splitMultiplicativeReduction := fun b =>
    X.S.arithmetic.curve.HasSplitMultiplicativeReductionAt (nativeBadLift X b)
  splitMultiplicativeReduction_proved := R.splitMultiplicativeReduction
  reductionCompatibility := by
    intro b hb
    exact X.S.arithmetic.curve.hasSplitMultiplicativeReductionAt_imp_multiplicative
      (R.splitMultiplicativeReduction b)
  qParameter := R.qParameter
  qParameter_nonzero := R.qParameter_nonzero
  qParameter_contracting := R.qParameter_contracting
  qParameter_reduction_compatibility := R.qParameter_reduction_compatibility

end LeanFormal.IUT.N8Closure.NativeReductionRestActual
