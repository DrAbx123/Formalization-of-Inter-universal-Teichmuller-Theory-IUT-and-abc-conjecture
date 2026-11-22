# S148: quotient normalized log-volume on O-times and combined log-volume

Date: 2026-10-29.

## Source log-shell identification

sourceLogShellNormalizedQuot u = [unitLog u] in K / unitLogRange.

normalizedLogVolumeQuot_on_units_eq_source proves that the S143d quotient
normalized log-volume on the embedded O-times equals this source log-shell
normalized log quotient:

  normalizedLogVolumeQuot dvrUniformizer (sourceOTimesToBoundary u)
    = sourceLogShellNormalizedQuot u.

The proof uses boundaryLogFormalFor_dvr_eq (the arbitrary-uniformizer formal log
at the S111 uniformizer is boundaryLogFormal) and boundaryLogFormal_ext_unit.

## Combined log-volume and the integer coordinate

combinedLogVolume pi hpi x = (quotient normalized part, n) in
(K / unitLogRange) x Z.

The first (quotient) component is the invariant normalized log-volume.  The
second component is the formal logPi integer exponent.

combinedLogVolume_uniformizer_change proves:

* first component invariant under pi -> pi';
* second component changes by n - n'.

Thus the extra integer coordinate is exactly the formal logPi exponent; it
enters the combined log-volume as the second component and is not killed by the
unit-log quotient.

No fake field log/sorry/axiom/True/PUnit.
