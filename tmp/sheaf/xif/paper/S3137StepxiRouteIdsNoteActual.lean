import LeanFormal.IUT.Audit.Status

/-! # S3137: stepxi route/registry INDEX ids note (next re-pin input; registry frozen)

stepxi-provided ids (all EXIT=0, checker CITABLE, probe results 154269 trio):
* INDEX.FT.C3.convention-consumer -> S3139C3ConventionRegionConsumerActual.sourceInd1Convention_reindex_image (152269);
* INDEX.FT.C3.convention-region-transfer -> S3139C3ConventionRegionTransferActual.sourceConventionRegion_transfer;
* INDEX.FT.C3.convention-neutral-region -> S3139ComparisonRegionNeutralActual.SourceConventionNeutralRegion/mem_transfer;
* INDEX.FT.route-composition -> S3139FirstTriangleRouteCompositionActual.firstTriangleRouteComposition + FirstTriangleRouteResidual;
* INDEX.FT.route-conclusion -> S3139FirstTriangleRouteConclusionActual.firstTriangleRouteConclusion;
* INDEX.FT.route-named-seams -> S3139RouteResidualNamedActual.firstTriangleRouteComposition_of_named;
* INDEX.TOOL.vendorAdapted.LGP-scalar-log-volume -> S3139TensorPacketScalarLogVolumeActual.sourceLGP_linearReadout_action;
* INDEX.TOOL.vendorAdapted.procession-log-volume -> S3139VendorProcessionLogVolumeActual.SourceProcessionTensorPacketLogVolume/logVolume_action;
* INDEX.TOOL.vendorAdapted.multiradial-procession-consumer -> S3139MultiradialProcessionConsumerActual.*;
* registry data: S3139RouteRegistryIdsActual.routeRegistryIds; vendor survey: S3139VendorSurveyActual.vendorSurveyFindings.
-/

namespace LeanFormal.IUT.Audit

/-- StepXI route ids for the next re-pin (data). -/
def S3137StepxiRouteIds : List (String × String) :=
  [ ("INDEX.FT.C3.convention-consumer", "S3139C3ConventionRegionConsumerActual.sourceInd1Convention_reindex_image (152269)"),
    ("INDEX.FT.C3.convention-region-transfer", "S3139C3ConventionRegionTransferActual.sourceConventionRegion_transfer"),
    ("INDEX.FT.C3.convention-neutral-region", "S3139ComparisonRegionNeutralActual.SourceConventionNeutralRegion/mem_transfer"),
    ("INDEX.FT.route-composition", "S3139FirstTriangleRouteCompositionActual.firstTriangleRouteComposition + FirstTriangleRouteResidual"),
    ("INDEX.FT.route-conclusion", "S3139FirstTriangleRouteConclusionActual.firstTriangleRouteConclusion"),
    ("INDEX.FT.route-named-seams", "S3139RouteResidualNamedActual.firstTriangleRouteComposition_of_named"),
    ("INDEX.TOOL.vendorAdapted.LGP-scalar-log-volume", "S3139TensorPacketScalarLogVolumeActual.sourceLGP_linearReadout_action"),
    ("INDEX.TOOL.vendorAdapted.procession-log-volume", "S3139VendorProcessionLogVolumeActual.SourceProcessionTensorPacketLogVolume/logVolume_action"),
    ("INDEX.TOOL.vendorAdapted.multiradial-procession-consumer", "S3139MultiradialProcessionConsumerActual"),
    ("registry", "S3139RouteRegistryIdsActual.routeRegistryIds"),
    ("vendor-survey", "S3139VendorSurveyActual.vendorSurveyFindings") ]

/-- INDEX record: stepxi route ids batch (next re-pin input). -/
def S3137StepxiRouteBatchRecord : Obligation :=
  { id := "S3137.index.stepxi-route-ids-batch"
    source := "stepxi message; S3139C3ConventionRegionConsumerActual etc.; probe results 154269"
    status := VerificationStatus.interface
    note := "STEPXI ROUTE IDS for next re-pin (all EXIT0 + checker CITABLE, probe 154269 trio): convention-consumer/region-transfer/neutral-region, first-triangle route composition/conclusion/named-seams, vendorAdapted LGP/procession/multiradial tool ids. Registry frozen; data note only."
    dependsOn := ["S3137StepxiRouteIdsNoteActual"] }

end LeanFormal.IUT.Audit
