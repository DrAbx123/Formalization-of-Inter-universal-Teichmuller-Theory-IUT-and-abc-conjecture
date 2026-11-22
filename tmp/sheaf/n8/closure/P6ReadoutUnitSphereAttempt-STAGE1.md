# P6Readout unit-sphere attempt

- Task: Wave8.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6ReadoutUnitSphereAttempt.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0.
- Named sorry: 1 (`unitSphereReadoutDonorExists_obligation`).

## Actual results

- `unitSphere : GlobalRegion X := fun v => {x | ‖x‖ = 1}`;
- `unitSphere_localLog_zero`: actual local log zero on the sphere;
- `unitSphere_measurable`: actual measurability from closed sphere.

## Conditional actual constructor

`P6Readout.ofUnitSphereDonor D` uses unitSphere as both reference and region.
It fills the 8 Adm conjuncts from the measurable sphere, donor mass bounds, and
pointwise zero local log.  It uses donor support/weight/dimension; no arbitrary
weight is chosen by the file.

## Exact missing donor

`UnitSphereReadoutDonor` requires per-place `0 < mu (unitSphere) < top` and
actual procession support/weights/dimensions.
`unitSphereReadoutDonorExists_obligation` is the theorem-level named sorry.

`P6ReadoutFromUnitSphereTarget := Nonempty (P6Readout X mu)`.
`P6ReadoutFromUnitSphereTarget_of_donor` proves the target from donor existence
via the actual constructor.

## Status

statement_compiles true; actual measurable sphere/local-log-zero and conditional
readout constructor; donor existence named sorry.  p-adic unit-sphere mass is
not supplied by a production constructor in the tree; no arbitrary weights.