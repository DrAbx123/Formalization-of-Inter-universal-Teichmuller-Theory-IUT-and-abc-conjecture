# P6 procession weight/dimension donor actual attempt

- Task: Wave11.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6ProcessionWeightDonorActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0.
- Named sorry: 1 (`processionWeightDimensionDonorActualTarget_obligation`).

## Production search

- `WeightedDeterminantPacket`
  (IUTIII/Corollary312/StepXI/HolomorphicHull/WeightedNormalization.lean):
  actual `hullLogDegree`, `denominator : label -> Nat+`, and actual
  normalized/weighted log-volume, indexed by a finite `label` type.
- `FinitePlaceSelectedPrimeWeightedVolume`: actual selected-prime tuple weights
  and `fullPrimeArithmeticTensorDimension`, indexed by tuple places.
- `ArithmeticQPilotLogVolume.selectedLogMagnitude`: conditional selected-place
  weights, not native-place weights.
- `NativeC1.valueGroupAt/localFieldAt`: only local value groups, no procession
  weight/dimension.

## Exact no-go

`ProcessionWeightDimensionDonorActualTarget : Prop :=
  `Nonempty (ProcessionWeightDimensionDonor X)`.
Named sorry: no production declaration supplies a support/weight/dimension on
`NativePlaces`, and no native-place-to-label/tuple index with exact weight and
dimension compatibility exists.  The direct actual construction is therefore
no-go at current interfaces.

No all-1, arbitrary weights, free Real or fake Type is introduced.

## Status

statement_compiles true; exact target named sorry; actual donor NOT constructed.