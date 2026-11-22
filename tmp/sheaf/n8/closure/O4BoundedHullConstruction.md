# O4 bounded hull construction

Date: 2026-10-24. Owner: logdescent. Lean: O4BoundedHullConstruction.lean.
Compile: lake env lean -j1 -R D:/lean -> EXIT=0, zero sorry.

## Actual construction

- boundedScalingUnits := sourceScalingUnits ∩ {degree <= 0}; an actual subset.
- boundedHull := holomorphicHull boundedScalingUnits possibleThetaPilotImageSet.
- boundedHullVolume := sourceSetVolume boundedHull;
  imageVolume := sourceImageVolume.

## Proved results

- nonpositiveSubmonoid: points of sourceLocalLogDegree <= 0 form a submonoid.
- nonpositiveSubmonoid_candidate: it is a candidate hull for boundedScalingUnits.
- boundedHull_nonpositive: if every theta-pilot image has nonpositive degree,
  the whole bounded hull has nonpositive degree (holomorphicHull_le).
- boundedHullVolume_eq_zero: under that image-side condition the bounded hull
  volume is zero.
- imageVolume_eq_zero: similarly the image volume is zero.
- boundedHull_volume_eq_imageVolume: hence boundedHull volume = image volume.

## Exact condition

Image-side nonpositivity is needed: the bounded scaling restriction only
removes positive scalings, not positive theta-pilot images.  If an image has
positive degree, its powers remain in the bounded hull and force unbounded hull
volume, so equality cannot be asserted; the exact hypothesis is himg (all
sourceThetaPilotPoint degrees <= 0, equivalently the q <= 1 image regime in the
production sign dichotomy).

No arbitrary scaling or hull is introduced.