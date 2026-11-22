/-!
# S3139: route-integration checklist update (data only; registry frozen except approved re-pins)

Status after the C3 closure and the two route-integration batches.

CONSTRUCTED (citable checker pending/full batch):
* C3 closure: S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds (CITABLE).
* C3 route consumers: sourceInd1Convention_reindex_image (S3139C3ConventionRegionConsumerActual);
  sourceConventionRegion_transfer (S3139C3ConventionRegionTransferActual);
  SourceConventionNeutralRegion.mem_transfer (S3139ComparisonRegionNeutralActual);
  SourceV2ComparisonRegion.mem_transfer/ofNeutral (S3139ComparisonRegionV2NeutralActual).
* Route composition: firstTriangleRouteComposition (S3139FirstTriangleRouteCompositionActual);
  firstTriangleRouteConclusion; firstTriangleRouteComposition_of_named (named M0/M1/stage4 seams);
  firstTriangleRouteComposition_of_qpilotM1 (qpilot M1 named residual);
  firstTriangleRouteComposition_of_mainlineM0 (mainline M0 named residual).
* Vendor-adapted tools: sourceLGP_linearReadout_action; SourceProcessionTensorPacketLogVolume
  (+logVolume_action); SourceLabelAveragedLogVolume / SourceWeightedLabelAveragedLogVolume;
  SourceMultiradialProcessionConsumer.

OPEN (route residual; exact names):
* M0 same-C F ~ F_mod — mainline R1 (SourceM0MainlineResidual).
* M1 — qpilot S3133M1ContractSeparatedMissing / S3133M1Remaining (iff proved) + capsule-label link
  (SourceM1QpilotResidual).
* stage4 unit map — S3136LGPGlobalUnitsToLocalUnitsActual.lgpGlobalUnitsToLocalUnits.
* fourth-triangle arithmetic inputs — signed Theta-hull value + (xi-f) inclusion (shehdd).

QUESTIONS for mainline/abc: V2 comparisonRegion def/field consuming the reindex-image equality;
comparison-invariance hypothesis naming if needed (honest: linear automorphism, no automatic volume invariance).

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteIntegrationChecklistUpdatedActual

/-- The updated route-integration checklist (item, status). -/
def routeIntegrationChecklist : List (String × String) :=
  [ ("C3.convention-identification", "RESOLVED (first real closure; CITABLE)"),
    ("C3.route-consumer-equality", "CONSTRUCTED sourceInd1Convention_reindex_image"),
    ("C3.region-transfer", "CONSTRUCTED sourceConventionRegion_transfer"),
    ("C3.neutral-region", "CONSTRUCTED SourceConventionNeutralRegion.mem_transfer"),
    ("C3.V2-shaped-region", "CONSTRUCTED SourceV2ComparisonRegion.mem_transfer/ofNeutral"),
    ("route.composition", "CONSTRUCTED firstTriangleRouteComposition (conditional)"),
    ("route.composition.named", "CONSTRUCTED _of_named / _of_qpilotM1 / _of_mainlineM0"),
    ("vendor.adapted", "scalar log-volume, procession log-volume, label-averaged log-volume, multiradial consumer"),
    ("route.comparison-invariance", "OPEN mainline S3131RouteComparisonInvarianceHypothesis / abc S3135ComparisonMeasureInvariance (explicit V2 residual)"),
    ("M0.same-C", "OPEN mainline R1"),
    ("M1.place-selection", "OPEN qpilot names + capsule-label link"),
    ("stage4.unit-map", "OPEN S3136LGPGlobalUnitsToLocalUnitsActual"),
    ("fourth-triangle.inputs", "OPEN signed Theta-hull value + (xi-f) inclusion") ]

end LeanFormal.IUT.XiFPaper.S3139RouteIntegrationChecklistUpdatedActual
