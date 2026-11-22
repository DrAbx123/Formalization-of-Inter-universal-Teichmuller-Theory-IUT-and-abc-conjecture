# S68: exact obstructions for the integral-ring equivalence and O-boundary log

Date: 2026-10-29.

## 1. CompletionIntegers vs Integers

CompletionIntegers place is

  (underlyingPrime place).adicCompletionIntegers K,

while the log-shell uses

  Integers (CommonPrimeCompletion place) =
  (NormedField.valuation).integer.

Both are valuation subrings of the same completion, but the source tree has no
theorem identifying them.  The direct membership rewrite
mem_adicCompletionIntegers exposes differing prime-index/instance data
(completionRationalPrime returns Nat.Primes; adicCompletionIntegers expects the
HeightOneSpectrum prime subtype), so the naive set equality proof fails.

Exact requirement recorded: CompletionIntegersRingEquivData — an actual ring
equivalence between the two integral rings.  No inhabitant is asserted.

## 2. O-boundary log

S63 supplies the unit map O-times -> O-boundary and the source unit logarithm
only on O-times.  A logarithm on nonunit elements of O-boundary is not supplied
by the source; the exact extension requirement is recorded as
OBoundaryLogExtension, with no inhabitant.

## Conclusion

Neither gap is closed by fabrication.  The exact obstruction objects and their
required nonemptiness propositions are recorded in S68.

No fake equivalence/log/sorry/axiom/True/PUnit.
