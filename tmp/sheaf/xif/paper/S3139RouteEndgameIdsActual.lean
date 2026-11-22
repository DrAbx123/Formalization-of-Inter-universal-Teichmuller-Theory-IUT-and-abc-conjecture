/-!
# S3139: route-endgame ids (data only; registry frozen 13129, no edits from this stream)

Ids produced by the endgame batch (vendor mining + route hardening + V2 consumer
integration) for the next approved reopen/re-pin.

VENDOR-ADAPTED (source-only vendor, re-proved with our objects):
* INDEX.FT.vendorAdapted.procession-log-volume-chain -> S3139VendorProcessionLogVolumeChainActual
  (SourceCapsuleFamilyLogVolume, SourceTensorPacketProductLogVolume + product_law,
   sourceTensorPacketProductLogVolume_increment; vendor IUTStage1SourceCore.lean:1256/1269/1277/1299/1392/1469).
* INDEX.FT.vendorAdapted.ind-action-laws -> S3139VendorIndActionLawsActual.SourceIndActionLaws +
  sourceIndActionLaws (constructed from S3139 multiradial quotient lemmas; vendor
  IUTStage1Theorem311.lean:251/258/266/290/298/305).
* INDEX.FT.vendorAdapted.cor312-stage1-comparison -> S3139VendorStage1ComparisonBridgeActual
  (SourceStage1Comparison + SourceCor312ComparisonData.stage1Comparison; vendor
  CorollarySchema.lean:85/94).

ROUTE HARDENING (exact residual list after C3 closure):
* INDEX.FT.route.capsule-label-residual -> S3139RouteCapsuleLabelResidualActual
  (SourceCapsuleLabelLinkResidual + firstTriangleRouteComposition_with_capsuleLabel).
* INDEX.FT.route.final-hardened-composition -> S3139RouteFinalCompositionHardenedActual
  (SourceRouteHardenedResidual {m0, m1, capsuleLabelLink, stage4UnitMap} +
   firstTriangleRouteFinalComposition; no convention hypothesis remains, no volume
   invariance silently assumed).
* V2 CONSUMER PATH: INDEX.FT.C3.v2-consumer-integration -> S3139V2ConsumerIntegrationActual
  (SourceV2ComparisonRegionConsumer + membership_and_volume: comparison membership
   transfer + region-volume neutrality given the explicit FT.route.comparison-invariance).

OPEN RESIDUAL LIST (unchanged): FT.route.comparison-invariance / FT.route.measure-invariance
(mainline/abc), M0 same-C, M1 qpilot names + capsule-label link, stage4 unit map,
fourth-triangle arithmetic inputs.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteEndgameIdsActual

/-- Endgame ids: (index id, declarations, file). -/
def routeEndgameIds : List (String × String × String) :=
  [ ("INDEX.FT.vendorAdapted.procession-log-volume-chain",
      "SourceCapsuleFamilyLogVolume, SourceTensorPacketProductLogVolume, sourceTensorPacketProductLogVolume_increment",
      "S3139VendorProcessionLogVolumeChainActual.lean"),
    ("INDEX.FT.vendorAdapted.ind-action-laws",
      "SourceIndActionLaws, sourceIndActionLaws", "S3139VendorIndActionLawsActual.lean"),
    ("INDEX.FT.vendorAdapted.cor312-stage1-comparison",
      "SourceStage1Comparison, SourceCor312ComparisonData.stage1Comparison",
      "S3139VendorStage1ComparisonBridgeActual.lean"),
    ("INDEX.FT.route.capsule-label-residual",
      "SourceCapsuleLabelLinkResidual, firstTriangleRouteComposition_with_capsuleLabel",
      "S3139RouteCapsuleLabelResidualActual.lean"),
    ("INDEX.FT.route.final-hardened-composition",
      "SourceRouteHardenedResidual, firstTriangleRouteFinalComposition",
      "S3139RouteFinalCompositionHardenedActual.lean"),
    ("INDEX.FT.C3.v2-consumer-integration",
      "SourceV2ComparisonRegionConsumer, membership_and_volume",
      "S3139V2ConsumerIntegrationActual.lean") ]

/-- The exact open residual list after the C3 closure (for the V2 route). -/
def routeOpenResidualList : List (String × String) :=
  [ ("FT.route.comparison-invariance", "mainline S3131RouteComparisonInvarianceHypothesis"),
    ("FT.route.measure-invariance", "abc S3135ComparisonMeasureInvariance"),
    ("FT.M0.same-C", "mainline R1 same-C identification"),
    ("FT.M1.place-selection", "qpilot S3133M1ContractSeparatedMissing / S3133M1Remaining"),
    ("FT.M1.capsule-label-link", "contract-separated Capsule j.val <-> Bad/V"),
    ("FT.stage4.unit-map", "S3136LGPGlobalUnitsToLocalUnitsActual.lgpGlobalUnitsToLocalUnits"),
    ("FT.fourth-triangle.inputs", "signed Theta-hull value + (xi-f) inclusion") ]

end LeanFormal.IUT.XiFPaper.S3139RouteEndgameIdsActual
