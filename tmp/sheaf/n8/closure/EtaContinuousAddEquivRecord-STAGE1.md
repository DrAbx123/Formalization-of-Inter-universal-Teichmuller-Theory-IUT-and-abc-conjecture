# Explicit ContinuousAddEquiv record: exact no-go

- Task: combine qoCompletionRingEquiv.toAddEquiv with qoCompletionHomeomorph.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaContinuousAddEquivRecord.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; two named sorries (exact gaps).

## Actual

- qoAddEquiv := (qoCompletionRingEquiv X).toAddEquiv, actual additive
  equivalence K ≃+ QCompletion.

## Exact gaps

- FunctionEqualityRecord: value-level equality between qoAddEquiv and
  qoCompletionHomeomorph.  Not proved: the homeomorph/ring-equivalence
  instance transparency makes the direct function equality fail to elaborate
  (homeomorph function expected CommonPrimeCompletion, AddEquiv function uses
  the NormalizedCompletion/Completion synonym).
- ContinuousAddEquivRecord: Nonempty (K ≃ₜ+ QCompletion).  Missing continuity
  of both directions as a packaged record.
- Consequently AddEquiv.isAddHaarMeasure_map and the pushforward normalization
  at O_Q cannot be instantiated.  No arbitrary transport/measure equality.