# S1400: D8 real cusp coordinate — exact first field

Date: 2026-10-30. Lean EXIT=0. No q=1/5/log q use.

## Exact first field

For the paper cusp S1330PaperCusp l S = Iut.OrbicurveBoundaryCusp S.cK:

  S1400EpsilonMap l S = S1383EpsilonMap l S
    = S1330PaperCusp l S -> Real

plus positivity, nonzero, cuspScaleOf, cuspScale positivity, epsilon*cuspScale
nonzero, and compatibility.  No actual epsilonOf is constructed from the
geometric cusp/sign quotient alone.

## Actual reused

* S1330ActualLogQ_ne_epsilon: q is not the positive epsilon; q=1/5 and
  log q are not used.
* S1330CuspRep_x_zero: actual projective cusp [0:1:0] has x=0, no positive
  x-coordinate.
* S1383/S1357 exact carrier/conditional constructor, reused not duplicated.

## Exact missing object

S1330RealCuspCoordinateMissing l S (real coordinate map + positivity/scale/
compat data).  Consumer: SourceCuspClause D8 via
S1330CuspClauseOfRealCuspCoordinate.

No weak Prop/Nonempty gate beyond the existing exact-required definition.
