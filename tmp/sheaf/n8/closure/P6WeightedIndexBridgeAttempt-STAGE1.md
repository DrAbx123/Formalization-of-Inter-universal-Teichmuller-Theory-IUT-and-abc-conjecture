# Weighted index -> NativePlaces bridge attempt

- Task: Wave12.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6WeightedIndexBridgeAttempt.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0.
- Named sorry: 1 (`weightedIndexBridgeActualTarget_obligation`).

## Actual partial bridge

- `nativePlaceOfFinitePlace (place : FinitePlace Fmod) : NativePlaces X.S`
  := `V_mod_bijection (NumberFieldPlace.finite place)`.
- `nativePlaceOfFinitePlace_comap` proves the base comap is the finite place.
- `nativeSupportOfFinset` transports an actual finite support through the
  bridge.

## Weight/dimension no-go

Production weight/dimension donors are not NativePlaces-indexed:
- `WeightedDeterminantPacket` has an arbitrary finite `label` index;
- `FinitePlaceSelectedPrimeWeightedVolume` weights are on tuple-indexed blocks
  and depend on the whole tuple `ι -> FinitePlaceAtPrime k p`.
There is no canonical label/tuple -> NativePlaces map with exact weights and
dimensions.  Therefore the actual `ProcessionWeightDimensionDonor` is not
constructed; `weightedIndexBridgeActualTarget_obligation` is the named sorry.
No arbitrary weights are chosen.

## Status

statement_compiles true; finite-place index bridge actual; weight/dimension
bridge exact no-go + named sorry.