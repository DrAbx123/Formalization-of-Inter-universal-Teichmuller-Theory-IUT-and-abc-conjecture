# S658: corrected root-normalized paper signed hull on S657 positive magnitude

Date: 2026-10-29. No import of S645.

## Construction

S657 provides the positive magnitude procession

  rootThetaMagnitudeProcession T b
    value j = (sum_v qVFamPaperThetaTensorCoefficient T b j) * log(qVFamTensorP T b)

with nonnegative values and nonnegative average.

S658 constructs

  rootNormalizedPaperSignedHullCorrected T b A hnormal : PaperSignedHull X (SignedLabel l.value)

with:
  ambient := A
  procession := rootThetaMagnitudeProcession T b
  hull := rootThetaMagnitudeFiniteHull T b
  weighted_matches_hull := rfl
  weights_nonnegative := inverse label cardinality nonnegative
  average_nonneg := rootThetaMagnitudeProcession_average_nonneg T b
  hull_logVolume_eq_average := hnormal.

## Signed log

rootNormalizedPaperSignedHullCorrected_signed_eq:
  signedHullLogVolume = -(rootThetaMagnitudeProcession T b).average.

Proof: unfold signedHullLogVolume, rewrite hnormal and
ENNReal.toReal_ofReal (average_nonneg).

No fake average/hnormal; no S645 import.
