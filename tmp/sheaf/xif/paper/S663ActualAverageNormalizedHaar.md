# S663: actual average-normalized Haar instantiation of S658

Date: 2026-10-30. S662 was not present; this file supplies the actual
arbitrary-average normalized Haar interface directly.

## Normalized Haar

For any actual additive Haar measure nu and target average a:

s663Scale a := exp(a - hullUnitLog - log nu(unitReference))
s663Measure a := ENNReal.ofReal (s663Scale a) * nu

s663Measure_isAddHaar: additive Haar.
s663Measure_unit_log:
  log ((s663Measure a) unitReference).toReal
    = a - arithmeticTupleHullUnitLogVolume.

## Actual IQ interface

s663Interface a :=
  (C6ActualIQData.actual places tuple (s663Measure a)).iqInterface

s663Interface_hull: hull = arithmeticTupleCanonicalHull.
s663Interface_logVolume_hull:
  interface.logVolume interface.hull = ENNReal.ofReal a.

## Elimination of A/hnormal from S658

s663Average T b := (rootThetaMagnitudeProcession T b).average.

s663PaperSignedHull :=
  S658 rootNormalizedPaperSignedHullCorrected T b
    (s663Interface s663Average)
    (s663Interface_logVolume_hull s663Average).

Thus A and hnormal are actual terms, not parameters. The only inputs are
places, tuple, and the actual Haar measure nu.

s663PaperSignedHull_signed_eq:
  signedHullLogVolume = -(rootThetaMagnitudeProcession T b).average.

No fake measure/Haar; no S645 import.
