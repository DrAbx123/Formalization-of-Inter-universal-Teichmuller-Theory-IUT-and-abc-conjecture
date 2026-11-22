# S1428: actual cusp / valuation / Haar / scale — exact first field

Date: 2026-10-31. Lean EXIT=0 (no sorry). File SHA256:

    ed44d811c617086b9d441202ecbadb260c4dd8a09a8d327bdae2333f5311ec94

No q = 1/5, no log q, no q-parameter substitution.

## Exact first field

For the faithful paper cusp

    S1330PaperCusp l S = Iut.OrbicurveBoundaryCusp S.cK

the exact first field is

    S1428EpsilonOf l S = S1400EpsilonMap l S
      = S1330PaperCusp l S -> Real.

This is stated by S1428EpsilonOf_eq_firstField.

## Actual cusp coordinate attempt (no-go)

The actual Gaussian cusp has representative [0 : 1 : 0].  Proved in
S1428RealCuspValuationActual.lean:

* S1428CuspRep_y_ne_zero: every representative has y != 0;
* S1428CuspAffineX_eq_zero / S1428CuspAffineZ_eq_zero: the affine x and z
  coordinates at the cusp are both zero;
* S1428CuspNormalizedY_eq_one: normalizing y to one gives the constant one;
* S1428CuspYFunction_constant: any scale-invariant function of the raw
  y-coordinate is constant on the cusp orbit.

Thus the projective cusp point alone yields no positive varying real
coordinate.  This is the precise obstruction for the "actual cusp coordinate"
route.

## Actual valuation / scale construction (conditional)

The actual completed local field at the concrete place above 5 is

    Completion (S1280Place l).

A cusp local parameter is a map

    localParameter : S1330PaperCusp l S -> Completion (S1280Place l)

with localParameter c != 0.  The construction sets

    epsilonOf c = || localParameter c ||,
    cuspScaleOf c = (|| localParameter c ||) ^ (-1).

The file proves:

* S1428ValuationEpsilonOf_pos / _ne_zero: positivity and nonzeroness;
* S1428ValuationCuspScaleOf_pos: positivity of the scale;
* S1428ValuationEpsilonOf_mul_scale: the invariant product is 1;
* S1428ValuationRealCuspCoordinate: the full S1330 real cusp coordinate;
* S1428ValuationCuspClause_epsilon: the existing source-clause constructor
  receives exactly the norm first field;
* S1428ValuationEpsilonOf_unit_mul: units of norm one do not change epsilon.

The construction depends only on the local norm/valuation scale, not on q or
on a chosen power of 5.

## Actual Haar construction (conditional, with bridge)

Given a Haar measure on the same completion and a measurable positive finite
region at each cusp, the file defines

    epsilonOf c = (mu (region c)).toReal.

The Haar coordinate S1428HaarRealCuspCoordinate is constructed, and
S1428HaarEpsilonOf_eq_valuation proves that it agrees with the valuation norm
whenever

    mu (region c) = ENNReal.ofReal || localParameter c ||.

## Exact missing input

The missing input left by both routes is an actual cusp local parameter:

    S1428CuspLocalParameter l S

containing the map to Completion (S1280Place l), its nonzero proof and the
semantic actuality proposition tying it to the paper cusp.  The bare
OrbicurveBoundaryCusp structure carries compactification data, not this local
parameter.  S1428CuspLocalParameterRequired states the exact nonemptiness
obligation; no inhabitant is asserted.

The consumer is S1330CuspClauseOfRealCuspCoordinate / SourceCuspClause D8.

## Axiom footprint

All checked declarations depend only on propext, Classical.choice and
Quot.sound.  No sorryAx appears in the final log.

## Compile command

    lake env lean tmp/sheaf/xif/paper/S1428RealCuspValuationActual.lean

EXIT=0.
