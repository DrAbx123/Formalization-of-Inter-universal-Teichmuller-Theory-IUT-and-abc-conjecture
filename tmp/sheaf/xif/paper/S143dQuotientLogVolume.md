# S143d: quotient normalized log-volume by the unit-log correction

Date: 2026-10-29.

## Construction

The actual correction subgroup is

  unitLogRange = range(unitLog) <= K,

an AddSubgroup of K.  The quotient normalized log-volume is

  normalizedLogVolumeQuot pi hpi x
    = [ first coordinate of boundaryLogFormalFor pi x ] in K ⧸ unitLogRange.

## Well-definedness

normalizedLogVolumeQuot_uniformizer_invariant proves that for any two
uniformizers pi, pi' and any x in O-boundary, the quotient classes agree.
The difference of the first coordinates is the actual unit-log difference
unitLog u - unitLog u', which lies in unitLogRange by construction.  Hence the
quotient normalized log-volume is well-defined independent of the chosen
uniformizer.

The integer formal-logPi coordinate is separate and is not quotiented by this
construction; only the normalized K-valued part is made invariant.

No fake quotient/invariance/sorry/axiom/True/PUnit.
