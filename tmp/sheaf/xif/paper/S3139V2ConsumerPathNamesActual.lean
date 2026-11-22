/-!
# S3139: V2 comparison-region consumer path — exact names (data only)

The exact consumer path agreed with mainline (FINAL-STATUS A22) and abc
(honesty flag), for the next approved reopen/INDEX update.

Paper-route side (mainline/abc, EXISTING; reuse, no re-proof):
* Cor312EpsilonArithmeticComparisonV2 (tmp/sheaf/xif/paper/Cor312ComparisonRegionV2Actual.lean:9)
  fields: comparisonRegion : Nat -> Nat -> Nat -> Set X; logShellPoint;
  logShellPoint_mem; height_le_comparisonRegionVolume; regionVolume_le_normalizedWeight.
* Cor312ToABCBridgeInterfaceV2 (same file :26) + cor312ToABCBridge_heightBoundV2 (:32)
  + production heightWeightBound_of_normalizedVolumeComparison
  (LeanFormal/IUT/ABCBridge/Bridge/ThetaBoundToHeightWeight.lean:67).
* Mainline A22 consumption point: V2 comparisonRegion + membership lemmas feeding
  height_le_comparisonRegionVolume; regionVolume_le_normalizedWeight and the
  height/volume dictionary must be on comparison-invariant source-side data or with
  the invariance hypothesis passed explicitly.

S3139 side (C3 convention-transfer entry; EXISTING in this stream):
* S3139C3ConventionRegionConsumerActual.sourceInd1Convention_reindex_image
  (explicit commuting-square equality: procession reindex image = comparison of
  polyIso in-place image).
* S3139C3ConventionRegionTransferActual.sourceConventionRegion_transfer
  (region membership transfer for comparison-invariant regions).
* S3139ComparisonRegionV2NeutralActual.SourceV2ComparisonRegion (+ mem_transfer/ofNeutral).
* S3139ComparisonRegionV2NeutralActual.SourceV2ComparisonRegion.logShellPoint_mem
  (V2 field-shape instance with the neutral condition).
* S3139V2ConsumerIntegrationActual.SourceV2ComparisonRegionConsumer
  (+ membership_and_volume: membership transfer AND region-volume neutrality given
  FT.route.comparison-invariance).
* Invariance residuals: mainline S3131RouteComparisonInvarianceHypothesis
  (S3139RouteComparisonInvarianceActual.SourceRouteComparisonInvariance) /
  abc S3135ComparisonMeasureInvariance (S3139ComparisonMeasureInvarianceResidualActual).

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139V2ConsumerPathNamesActual

/-- The exact consumer-path name mapping (paper-route name, S3139 name). -/
def v2ConsumerPathNames : List (String × String) :=
  [ ("Cor312EpsilonArithmeticComparisonV2.comparisonRegion",
      "S3139ComparisonRegionV2NeutralActual.SourceV2ComparisonRegion"),
    ("comparisonRegion membership lemmas (height_le_comparisonRegionVolume)",
      "S3139C3ConventionRegionConsumerActual.sourceInd1Convention_reindex_image + S3139C3ConventionRegionTransferActual.sourceConventionRegion_transfer"),
    ("regionVolume_le_normalizedWeight + height/volume dictionary",
      "S3139V2ConsumerIntegrationActual.SourceV2ComparisonRegionConsumer.membership_and_volume (given explicit invariance)"),
    ("S3131RouteComparisonInvarianceHypothesis (mainline)",
      "S3139RouteComparisonInvarianceActual.SourceRouteComparisonInvariance"),
    ("S3135ComparisonMeasureInvariance (abc)",
      "S3139ComparisonMeasureInvarianceResidualActual.S3135ComparisonMeasureInvariance") ]

end LeanFormal.IUT.XiFPaper.S3139V2ConsumerPathNamesActual
