# S132: normalized formal boundary log and source log-shell logMap

Date: 2026-10-29.

## Definitions

boundaryLogNormalized x = first coordinate of boundaryLogFormal x
(= unitLog u for the DVR decomposition x = u * pi^n).

boundaryLogInteger x = second coordinate (= n).

## Source log-shell compatibility (proved)

boundaryLogNormalized_eq_sourceLogMap:
for u in O-times,

  boundaryLogNormalized (sourceOTimesToBoundary u)
    = Multiplicative.toAdd ((sourceLocalLogShellDatum place).logMap u).

This uses boundaryLogFormal_ext_unit and unitLogHom_toAdd_apply; the source
log-shell datum's logMap is the actual integral-unit logarithm.

## Uniformizer change

For pi, pi' and the actual decompositions,

  boundaryLogFormalFor pi x - boundaryLogFormalFor pi' x
    = (n - n') • (0,1) + (unitLog u - unitLog u', 0).

The integer coordinate changes by n - n' (the formal logPi coordinate).  The
normalized/first coordinate changes by the actual unit-log difference
unitLog u - unitLog u', not by zero.  Thus the normalized part is not declared
invariant under uniformizer change without quotienting/identifying the unit-log
correction; doing so would discard actual log content.  This exact correction is
recorded in boundaryLogFormalFor_change_normalized and
boundaryLogFormalFor_change_integer.

No fake field logarithm/sorry/axiom/True/PUnit.
