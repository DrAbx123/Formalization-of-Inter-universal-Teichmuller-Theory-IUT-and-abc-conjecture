# S79: actual CompletionIntegers ≃+* Integers equivalence

Date: 2026-10-29.

## Construction

FinitePlaceNormalizedIntegers proves

  normalizedCompletion_norm_le_one_iff :
    ||normalizedCompletionRingEquiv place x|| <= 1 <-> ||x|| <= 1

and

  mem_completionIntegers_iff_norm_le_one :
    x in CompletionIntegers place <-> ||x|| <= 1.

S79 uses these to prove the carrier equality

  completionIntegersCarrierEq : forall x,
    x in CompletionIntegers place <-> x in Integers completion,

by composing the two unit-ball equivalences.  It then applies S77's
completionIntegersRingEquivOfCarrierEq to obtain the actual ring equivalence

  completionIntegersEquivIntegers :
    CompletionIntegers place ≃+* Integers (CommonPrimeCompletion place).

The equivalence is the identity on underlying completion elements
(completionIntegersEquivIntegers_coe, rfl).

## Status

S77 carrier hypothesis is closed; unconditional actual ring equivalence is
constructed and compiles.

No fake equality/sorry/axiom/True/PUnit.
