# Normalized Haar transport attempt at the actual F completion

- Task: push normalized Haar through actual completion homeomorph.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaNormalizedHaarTransportActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; one named sorry.

## Actual

- qoCompletionHomeomorph : K X ≃ₜ QCompletion X, from
  commonPrimeCompletionActualHomeomorph (nativeFPlaceAtPrime X).
- qoCompletionRingEquiv : K X ≃+* QCompletion X, from
  normalizedCompletionRingEquiv nativeFPlaceOverBad.
- qoCompletionIntegersEquiv : Integers (K X) ≃+* CompletionIntegers
  nativeFPlaceOverBad, from normalizedCompletionIntegersEquiv.

## Exact gap

The actual homeomorphism is only topological; the actual normalized integer
equivalence targets CompletionIntegers, not the canonical Integers(QCompletion)
ball at which muQ is normalized.  Missing actual theorem: a continuous additive
equivalence preserving the canonical integral balls (and the corresponding
Measure.map Haar theorem for it).  NormalizedHaarTransportTarget is the named
sorry; no arbitrary homeomorphism or measure equality is used.