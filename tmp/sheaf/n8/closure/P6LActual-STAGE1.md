# P6L actual readout attempt

- Task: Wave2 actual P6L instance.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6LActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0.
- One named sorry: `p6LActualReadoutTarget_obligation`.

## Actual available data reused

- `NativePlaces X.S` and `localFieldAt X v` (native place/local field family);
- `P6L.localLog` = `Real.log ‖x‖`; `actualLocalLog_eq` rfl;
- `P6L.GlobalCarrier`/`GlobalRegion` aliases;
- actual local Haar measure `mu` with `IsAddHaarMeasure` as a parameter.

## Target

`P6LActualReadoutTarget : Prop := Nonempty (P6L.P6Readout (X := X) (mu := mu))`.
This is exactly the existing P6L readout type, not a new free structure.
`P6LActualReadoutTarget_iff_p6ReadoutExists` is Iff.rfl with P6L's target.

## Why no actual instance constructed

No actual admissible region family with positive finite Haar mass and
almost-everywhere zero local log, no actual procession weights/dimensions,
and no reference calibration are present in the tree.  Candidate obstructions:
- full local field is not finite positive mass under Haar;
- norm-one/unit region is null for additive Haar and no positive-mass
  a.e.-zero-log region is constructed;
- no actual weight/dimension/reference data.

Thus the exact target is registered with theorem-level named sorry
`p6LActualReadoutTarget_obligation`; no free Real/Set or fake data.

## Status

statement_compiles true; actual local log/carrier reused; actual P6Readout
instance NOT constructed; named sorry only.  No math closure claimed.