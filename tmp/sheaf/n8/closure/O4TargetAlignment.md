# O4 target alignment: actual hull unit vs source ellOut

Date: 2026-10-24. Owner: logdescent. Lean: O4TargetAlignment.lean.
Compile: lake env lean -j1 -R D:/lean -> EXIT=0, zero sorry.

## Exact result

Source ellOut is J.B.normalizedLogVolume J.region.  The actual canonical hull
unit readout is arithmeticTupleHullUnitLogVolume J.C3.tensorPlaces
J.C3.tensorTuple.  Production gives

  normalizedLogVolume canonicalHull
    = (1 / finrank) * arithmeticTupleHullUnitLogVolume.

Therefore the exact condition for ellOut(J) = hullUnitLogVolume(J) is:

1. J.region = arithmeticTupleCanonicalHull (canonicalHullRegion);
2. J.B.normalizedLogVolume = arithmeticTupleNormalizedLogVolume (actual C6
   normalization; C6NormalizationLink);
3. the tensor block relative degree is 1.

`ExactAlignmentCondition` packages (1), (2), (3).
`ellOut_eq_hullUnit_of_condition` proves the conditional alignment.
`ellOut_eq_hullUnit_iff_of_conditions` proves the decisive characterization:
under (1),(2), equality holds iff finrank=1 or hullUnitLogVolume=0.

## Decisive no-go

Without (1),(2),(3), unconditional alignment is not a theorem: condition (2)
is not definitional (J.B is C6 data, not definitionally the production
normalization), and production's 1/finrank factor obstructs the hull-unit
identification unless finrank=1 or the hull volume is zero.  No new local
readout is introduced; Θ/ellOut alignment is exactly the condition above.