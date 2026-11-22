# P6 nonarchimedean unit-sphere attempt

- Task: Wave10.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6ReadoutNonarchSphereAttempt.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0.
- Named sorry: 1 (`processionWeightDimensionDonorExists_obligation`).

## Actual nonarch mass theorem

`nonarch_unitSphere_mass_pos_lt_top` proves for every native place in the
ultrametric local field:
`0 < mu v (unitSphere v) ∧ mu v (unitSphere v) < top`.
Proof: unit sphere = Metric.sphere 0 1; `IsUltrametricDist.isOpen_sphere` gives
open, nonempty interior at 1 gives positive Haar mass, compactness gives
finite mass.  This is actual (zero sorry) under the stated ultrametric/proper/
Haar instances.

## Full donor

`ProcessionWeightDimensionDonor` records the remaining actual support/weights/
dimensions.  `unitSphereReadoutDonorOfWeights` builds the full
`UnitSphereReadoutDonor` using the actual mass theorem and donor data; no
weight is chosen by this file.

`processionWeightDimensionDonorExists_obligation` is the named sorry: no
production source supplies actual procession support/weights/dimensions.

`nonarchUnitSphereReadoutDonorExists_of_weights` derives full donor existence
from the weight donor; `P6ReadoutFromNonarchUnitSphere` gives the conditional
P6L readout via the Wave8 constructor.

## Archimedean branch

Reused Wave8b `noUnitSphereReadoutDonor_of_archimedean`: an archimedean native
place blocks a full donor (sphere has zero additive Haar mass).  Not retried.

## Status

statement_compiles true; nonarch unit-sphere positive finite Haar mass actual;
full donor conditional on actual weights/dims donor named sorry; archimedean
no-go reused.