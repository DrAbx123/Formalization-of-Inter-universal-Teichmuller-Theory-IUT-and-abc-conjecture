# Normalized Haar transport 2: Integers/CompletionIntegers comparison

- Task: check defeq/rfl of Integers(QCompletion) and CompletionIntegers.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaNormalizedHaarTransportActual2.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; one named sorry.

## Defeq check

Not defeq/rfl: `Integers (QCompletion X)` is a Subring, while production
`CompletionIntegers (nativeFPlaceOverBad X)` is a ValuationSubring (different
types; the set-coercion is not rfl).

## Actual bridge

- O_Q_set_eq: the underlying carrier sets are equal: both are the norm<=1
  ball.  Proof uses mem_integers_iff and the production theorem
  mem_completionIntegers_iff_norm_le_one.

## Exact gap

Turning the set equality into a normalized measure transport still needs the
missing actual continuous additive equivalence preserving the integral balls,
plus the corresponding Measure.map Haar invariant theorem.  The target
NormalizedHaarTransportTarget2 is the named sorry.  No arbitrary transport or
measure equality is used.