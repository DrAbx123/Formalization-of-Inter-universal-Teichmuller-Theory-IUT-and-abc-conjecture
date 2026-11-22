# S150: source log-volume normalization for the combined formal log-volume

Date: 2026-10-29.

## Actual normalization data

sourceLogVolumeScale = (logShellScale p : K).

sourceLogShellNormalizedMap u = scale^{-1} * unitLog u.

sourceLogShellNormalizedQuotScaled u = [sourceLogShellNormalizedMap u] in
K / unitLogRange.

SourceLogVolumeNormalization packages the scale, the normalized map, the
quotient map, and the integer formal-logPi alignment; sourceLogVolumeNormalization
is the actual package.

## O-times comparison

combined_quotient_on_units_eq_source proves that the unscaled S143d quotient
normalized log-volume on embedded O-times equals the source log-shell quotient
of unitLog (via S148).

## Integer logPi coordinate

combined_integer_coordinate_alignment proves that the combined log-volume's
integer coordinate is exactly the second coordinate of boundaryLogFormal.  It is
the formal DVR exponent n, separate from the K-valued log-shell scale.

## Exact alignment gap

The log-shell scale is a K-valued factor, while K/unitLogRange is only an
additive quotient group; multiplying a quotient class by a non-unit K factor is
not well-defined without extra module structure.  Therefore no theorem
identifies the scaled source quotient with the unscaled combined quotient; this
is stated as an exact gap rather than faked.

No fake field log/sorry/axiom/True/PUnit.
