# Normalized Haar transport 3: attempt and exact no-go

- Task: push μK to QCompletion via actual ring/homeomorph, prove Haar image and
  O_Q normalization, then Haar uniqueness equals μQ.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaNormalizedHaarTransportActual3.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; one named sorry.

## Actual inputs

- qoAddEquiv := (qoCompletionRingEquiv X).toAddEquiv, actual additive
  equivalence K ≃+ QCompletion.
- qoCompletionHomeomorph actual topological homeomorphism.
- O_Q_set_eq actual set equality of the integral balls.

## Exact no-go / missing theorems

- No production continuity instance for qoAddEquiv in both directions
  compatible with AddEquiv.isAddHaarMeasure_map; the actual homeomorphism is
  only topological and its function does not match the AddEquiv function at
  the instance level used by the Lean elaboration.
- Consequently the pushforward Haar proof (Measure.map +
  AddEquiv.isAddHaarMeasure_map) and the normalized-Haar uniqueness step are
  not instantiable without an explicit continuous-additive-equivalence record.
- PushedHaarEqualsMuQTarget is the named sorry (the exact target).

No arbitrary transport or measure equality is used.