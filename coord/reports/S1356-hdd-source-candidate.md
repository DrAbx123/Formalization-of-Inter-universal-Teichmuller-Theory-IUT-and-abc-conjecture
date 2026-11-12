# S1356: true HDD source candidate

Date: 2026-10-30
Lean: tmp/sheaf/xif/paper/S1356HDDHullDetSourceActual.lean
EXIT=0; SHA256 F68B2A62090FC254A1330E44B7767B5CD5CFD0C05DE400EA576BFB0400948A34.

## Attempt

Actual donors available:
- LocalFieldProductHull.hull, integralSpan_eq_hull, measure laws;
- S1300ActualHullDetSpec and s1300ActualHullDetSpec_holds;
- HullDeterminantLogVolumeFrozenSpec and its actual proof;
- DetTensorPowerLogVolumeBookkeeping (bookkeeping only).

Cannot construct S1300HDDHullDetSource's E/image/compact/coordinate/det:
- E: no finite family independent of place v with ring equivalence to every
  localField v; local fields depend on v.
- image: LocalFieldProductHull consumes an arbitrary Set; it supplies no
  output-dependent actual image family.  compact_closure/nonempty/coordinate
  all depend on that missing image.
- detData: DetTensorPowerLogVolumeBookkeeping is a bookkeeping interface;
  only the scalar calibration exists, not the paper HDD carrier.

## Exact first field

S1356HDDSourceRequired := S1300HDDHullDetSource I;
S1356UniformLocalEquiv rank E :=
  forall v : FinitePlace Q, (i : Fin rank) -> E i ≃+* localField v.

No inhabitant. Conditional actual s1356LatticeOfSource: a supplied S1300
source gives S1215HDDLocalLattice via LocalFieldProductHull.hull. No
rank-one/Fin 1/arbitrary Set.
