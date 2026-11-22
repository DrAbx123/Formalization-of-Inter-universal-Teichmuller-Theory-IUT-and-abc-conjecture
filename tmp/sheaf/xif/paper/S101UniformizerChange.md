# S101: uniformizer-change formula for boundaryLogWith

Date: 2026-10-29.

## Actual formula

For two uniformizers pi, pi' of the DVR Integers K, the actual decompositions
of x in O-boundary are

  x = u * pi^n = u' * pi'^n'.

The actual boundary log is boundaryLogWithFor pi logPi x = n • logPi +
unitLog u.  Therefore

  boundaryLogWithFor pi logPi x - boundaryLogWithFor pi' logPi' x
    = n • logPi - n' • logPi' + (unitLog u - unitLog u').

This is proved as boundaryLogWithFor_change, with the unit-log difference
explicit as unitLogCorrection.

## Not merely an integer multiple of logPi

The correction term unitLog u - unitLog u' is generally present.  The formula
does not assert that the difference is an integer multiple of a single logPi;
doing so would skip the unit-log term.  The exact correction is recorded, not
discarded.

No fake formula/sorry/axiom/True/PUnit.
