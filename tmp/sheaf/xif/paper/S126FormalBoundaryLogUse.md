# S126: formal boundary log on O-boundary and log-shell use

Date: 2026-10-29.

## Log-shell/O-times compatibility

logShellLogFormal u = (unitLog u, 0).

boundaryLogFormal_agrees_logShellLog proves that on the embedded O-times,

  boundaryLogFormal (sourceOTimesToBoundary u) = logShellLogFormal u.

Thus the O-times log-shell logarithm is exactly the first coordinate of the
formal boundary log.

## Full O-boundary formal log

S111's boundaryLogFormalHom is the complete O-boundary log with formal
logPi = (0,1).  boundaryLogFormalFor generalizes it to an arbitrary
uniformizer, and boundaryLogFormalFor_change proves the formal change formula

  boundaryLogFormalFor pi x - boundaryLogFormalFor pi' x
    = (n - n') • (0,1) + (unitLog u - unitLog u', 0).

Only the formal logPi coordinate and the unit-log first coordinate change; no
field-valued log(pi) is used.

No fake field logarithm/sorry/axiom/True/PUnit.
