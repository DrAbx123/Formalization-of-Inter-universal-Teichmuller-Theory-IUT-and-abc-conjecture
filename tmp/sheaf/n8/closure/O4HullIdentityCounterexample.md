# O4 explicit hull-identity counterexample

Date: 2026-10-24. Owner: logdescent. Lean: O4HullIdentityCounterexample.lean.
Compile: lake env lean -j1 -R D:/lean -> EXIT=0, zero sorry.

## Explicit objects (under pointwise degree faithfulness hdeg)

- scalingUnit := I.constantThetaPilotPoint v R (ofAdd 1).
- imagePoint := I.sourceThetaPilotPoint v R n (zero label) = 1.
- hullPoint := scalingUnit * imagePoint.

Theorems (actual, given hdeg):
- scalingUnit_mem_sourceScalingUnits: constant point of exponent 1 is in
  sourceScalingUnits (production theorem constantThetaPilotPoint_mem_sourceScalingUnits).
- scalingUnit_mem_hull / imagePoint_mem_hull.
- hullPoint_mem_hull: s*image lies in the actual source holomorphic hull
  (sourceHolomorphicHull_scaling_mem).
- hullPoint_logDegree_pos: sourceLocalLogDegree hullPoint > 0; value is
  card(sourceVolumeIndex l) > 0 (image point contributes 0).
- not_ViaImagesIdentity_of_degreeFaithful: therefore the via-images identity
  hull volume = image volume fails (using O4ConstructedHull no-go theorem).

## Exact obstruction

SourceImageRealization provides degree_of_q only at q, not pointwise degree
faithfulness for every real exponent.  PointwiseDegreeFaithfulnessObstruction
records the exact input needed for the explicit positive scaling unit and the
counterexample.  No arbitrary hull/readout is used.