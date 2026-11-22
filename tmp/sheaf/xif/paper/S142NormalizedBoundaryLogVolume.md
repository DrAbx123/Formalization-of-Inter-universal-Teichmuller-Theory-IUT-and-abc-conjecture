# S142: normalized O-boundary log-volume from formal boundary log

Date: 2026-10-29.

## Definition

For x in O-boundary,

  boundaryLogVolumeNormalized x
    = (logShellScale p)^{-1} * boundaryLogNormalized x
    = (logShellScale p)^{-1} * unitLog u

for the DVR decomposition x = u * pi^n.  The integer formal-logPi coordinate n
is separate (boundaryLogFormal integer coordinate).

## Source log-shell compatibility

On O-times, boundaryLogVolumeNormalized_eq_sourceLogMap proves

  boundaryLogVolumeNormalized (sourceOTimesToBoundary u)
    = (logShellScale p)^{-1} *
        Multiplicative.toAdd ((sourceLocalLogShellDatum place).logMap u).

This is the actual scaled source integral-unit log coordinate, using
sourceLogShellLog.

## Uniformizer change

Changing pi to pi':

* integer coordinate changes by n - n' (formal logPi coordinate);
* normalized K-valued coordinate changes by

  (logShellScale p)^{-1} * (unitLog u - unitLog u').

Thus the normalized coordinate is invariant **only** under the exact condition
NormalizedInvariantCondition, i.e. when the unit-log correction vanishes or is
quotiented.  No fake invariance is asserted.

No fake field log/real log-volume/sorry/axiom/True/PUnit.
