# Unit-sphere readout donor actual attempt

- Task: Wave8b.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/UnitSphereReadoutDonorActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0.
- Named sorries: 2 (`archimedean_unitSphere_mass_zero`, `unitSphereReadoutDonorActualTarget_obligation`).

## Actual results

Reuses Wave8 `unitSphere` (measurable, local log zero).

- `HasArchimedeanNativePlace` exact predicate;
- `archimedean_unitSphere_mass_zero`: additive Haar mass of the norm-one sphere
  at a native archimedean place is zero (named sorry; no production native
  archimedean instance theorem);
- `noUnitSphereReadoutDonor_of_archimedean`: actual conditional no-go: if such
  a place exists, no `UnitSphereReadoutDonor` (positive sphere mass contradicts
  zero mass).
- `UnitSphereReadoutDonorActualTarget := Nonempty UnitSphereReadoutDonor`;
  named sorry.
- `P6ReadoutActualTarget_of_donor`: conditional P6Readout from donor via Wave8
  constructor.

## Why no unconditional actual donor

The unit sphere at archimedean native places has zero additive Haar mass; at
nonarchimedean places a positive finite sphere mass and actual procession
weights/dimensions are still not constructed.  No arbitrary weights are chosen.

## Status

statement_compiles true; archimedean obstruction and conditional no-go actual;
unconditional donor actual target named sorry.  No actual P6Readout constructed.