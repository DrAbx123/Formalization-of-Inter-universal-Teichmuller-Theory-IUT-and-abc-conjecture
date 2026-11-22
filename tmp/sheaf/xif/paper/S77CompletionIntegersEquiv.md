# S77: integral-ring equivalence — exact obstruction and transport API

Date: 2026-10-29.

## Attempt

Both integral rings live on the same completion but are defined from different
norm instances:

* CompletionIntegers place = adic-completion integral ring, with the adic
  valued-field norm;
* Integers (CommonPrimeCompletion place) = unit ball of the normalized spectral
  norm on CommonPrimeCompletion.

The source file FinitePlaceNormalizedCompletion explicitly states that
integer-ring compatibility is a separate theorem; a homeomorphism alone does not
identify unit balls.  No theorem in the frozen tree proves that the two unit
balls have the same elements.

## Actual transport API

S77 defines

  completionIntegersCarrierEq : Prop :=
    forall x, x in CompletionIntegers place <-> x in Integers completion

and, from this hypothesis, the actual identity RingEquiv

  completionIntegersRingEquivOfCarrierEq :
    CompletionIntegers place ~=+ Integers completion.

The hypothesis is left as the exact required source fact
(completionIntegersCarrierEqRequired); no inhabitant is asserted.

## Conclusion

The unconditional ring equivalence is not constructed; the exact missing
carrier equality is the obstruction.  The conditional identity equivalence is
actual and compiles.

No fake equivalence/sorry/axiom/True/PUnit.
