# Root hull closure equality is unnecessary

Date: 2026-10-29. Direction correction only; no Lean compilation.

## Decision

Do not prove

  rootThetaHull = closure(union_j F(j^2 c_root) O_hol) = F(c_root) O_hol.

The target uses rootThetaHull itself.  The closedness/equality of the closure
with the maximal j = 1 region is not needed for the containment/monotonicity
route:

  qPilotRootRegion subset rootThetaHull
  arithmeticTupleNormalizedLogVolume_mono
  => qPilotSigned <= rootThetaHullLog.

## Files affected

- tmp/sheaf/xif/paper/RootHullClosednessActual.lean: created for the equality/
  closedness route but not queued; marked unnecessary, do not extend.
- tmp/sheaf/xif/paper/RootNormalizedThetaHullActual.lean: its root hull/formula
  data is actual, but the RootThetaHullNormalizedLog equality-gap route is not
  needed; removed from the active compile queue to avoid supporting the
  unnecessary equality target.

## Retained route

- tmp/sheaf/xif/paper/RootHullContainmentInequalityActual.lean (local compile
  EXIT=0): qPilotClassicalRegion subset rootThetaHull and
  qPilotClassicalLog <= rootThetaHullLog via normalized-log monotonicity.

No equality, no closedness claim, and no fake hull identification is asserted.
