/-!
# S3139: model-route ids (data only; registry frozen 13129, no registry edits)

Ids for the next approved reopen/INDEX update after the Option-B model-route batch.

* INDEX.FT.model-route.M1-discharge (in-model, Option-B) -> S3139ModelM1DischargeActual:
  sourceModelM1Evidence, sourceModelM1Evidence_holds, sourceModelM1_treeModel_constructible,
  sourceModelM1_vBasis_constructible, firstTriangleRouteResidualModelM1,
  firstTriangleRouteResidualModelM1_placeSelection.
  Evidence: S3133ExistingModelAdaptationActual.S3133TreeModelM1Datum/_constructible
  (results:159686); S3133ModelM1PlaceToModActual.modelPlaceToModDatum/_injective/_constructible
  (results:155535).
* INDEX.FT.model-route.haar-CardHull-consumption -> S3139HaarModelConsumptionActual:
  s3139_treeModelHaarData_scaling, s3139_treeModel_theta_q,
  s3139_modelHullVolume_le_imageVolume, SourceModelRouteEvidence + sourceModelRouteEvidence.
  Evidence: S3133ExistingModelAdaptationActual (tree model over SourceUnitRegionHaarDataActual:
  sourceHaarActualFamily:322/OriginalInput:346/ImageRealization:374/Data:416);
  CardHullRealSignedLogVolume.sourceSignedHullLogVolume_le_sourceSignedImageLogVolume:215;
  S3135ModelSkeletonInterfaceActual (model hull/Haar/scaling interface).
* INDEX.FT.route.residual-v3 -> S3139RouteResidualUpdateV3Actual.routeOpenResidualsV3
  (FT.M1 in-model DISCHARGED; remaining: general M1, capsule-label link, M0, stage4 map,
  fourth-triangle arithmetic inputs, comparison/measure invariance).
* INDEX.TOOL.vendorAdapted.source-core-container-estimates -> S3139VendorSourceCoreEstimatesActual
  (SourceLocalContainerLogVolumeEstimate / SourceLocalObjectContainerLogVolumeEstimate;
  vendor IUTStage1SourceCore.lean:1109/1121).
* INDEX.REUSE.model-route-audit -> S3139PriorArtAudit2Actual.modelRoutePriorArt.

Also already available (batch 4): S3139VendorProcessionLogVolumeChainActual,
S3139VendorIndActionLawsActual (vendor log-volume chain + Theorem311 ind-action laws
adapted and citable; no further re-proof needed).

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteModelIdsActual

/-- Model-route ids: (index id, declarations, file). -/
def routeModelIds : List (String × String × String) :=
  [ ("INDEX.FT.model-route.M1-discharge",
      "sourceModelM1Evidence, sourceModelM1Evidence_holds, firstTriangleRouteResidualModelM1",
      "S3139ModelM1DischargeActual.lean"),
    ("INDEX.FT.model-route.haar-CardHull-consumption",
      "s3139_treeModelHaarData_scaling, s3139_treeModel_theta_q, s3139_modelHullVolume_le_imageVolume, SourceModelRouteEvidence, sourceModelRouteEvidence",
      "S3139HaarModelConsumptionActual.lean"),
    ("INDEX.FT.route.residual-v3", "routeOpenResidualsV3",
      "S3139RouteResidualUpdateV3Actual.lean"),
    ("INDEX.TOOL.vendorAdapted.source-core-container-estimates",
      "SourceLocalContainerLogVolumeEstimate, SourceLocalObjectContainerLogVolumeEstimate",
      "S3139VendorSourceCoreEstimatesActual.lean"),
    ("INDEX.REUSE.model-route-audit", "modelRoutePriorArt",
      "S3139PriorArtAudit2Actual.lean") ]

end LeanFormal.IUT.XiFPaper.S3139RouteModelIdsActual
