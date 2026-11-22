/-!
# S3139: first-triangle route registry ids (data only; registry frozen except approved re-pins)

Ids for the next approved reopen/re-pin, after the C3 closure and this batch.

RESOLVED (THEOREM nodes):
* FT.C3.convention-identification -> S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds (results:151396, CITABLE).
* FT.C3.convention-consumer -> S3139C3ConventionRegionConsumerActual.sourceInd1Convention_reindex_image (results:152269).
* FT.C3.convention-region-transfer -> S3139C3ConventionRegionTransferActual.sourceConventionRegion_transfer.
* FT.route-composition -> S3139FirstTriangleRouteCompositionActual.firstTriangleRouteComposition.
* FT.route-conclusion -> S3139FirstTriangleRouteConclusionActual.firstTriangleRouteConclusion.
* TOOL.piTensorEntryPermute -> S3139ToolsPiTensorEntryPermute.piTensorEntryPermute/_tprod (results:150781, CITABLE).
* TOOL.vendorAdapted.LGP-scalar-log-volume -> S3139TensorPacketScalarLogVolumeActual.sourceLGP_linearReadout_action.
* TOOL.vendorAdapted.multiradial-procession-consumer -> S3139MultiradialProcessionConsumerActual.SourceMultiradialProcessionConsumer/_consumer.

OPEN (route residual):
* M0/R1 same-C identification F ~ F_mod (mainline R1).
* M1/R1 place selection (qpilot S3133M1ContractSeparatedMissing / S3133M1Remaining; iff proved) + capsule-label link (contract-separated).
* stage4 canonical unit map (S3136LGPGlobalUnitsToLocalUnitsActual.lgpGlobalUnitsToLocalUnits).
* fourth-triangle arithmetic inputs (signed Theta-hull value + (xi-f) inclusion; shehdd route).

VENDOR SURVEY (source-only, not importable): see S3139VendorSurveyActual.vendorSurveyFindings
(file:line + names + our adapted declaration).

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteRegistryIdsActual

/-- One registry id entry for the next approved re-pin. -/
structure RouteRegistryId where
  indexId : String
  declarations : List String
  file : String
  status : String

/-- Registry ids produced by the C3 closure and this route batch. -/
def routeRegistryIds : List RouteRegistryId :=
  [ { indexId := "INDEX.FT.C3.convention-identification",
      declarations := [ "sourceInd1ConventionIdentification_holds" ],
      file := "S3139C3ConventionClosureActual.lean", status := "RESOLVED THEOREM" },
    { indexId := "INDEX.FT.C3.convention-consumer",
      declarations := [ "sourceInd1Convention_reindex_image" ],
      file := "S3139C3ConventionRegionConsumerActual.lean", status := "CONSTRUCTED" },
    { indexId := "INDEX.FT.C3.convention-region-transfer",
      declarations := [ "sourceConventionRegion_transfer" ],
      file := "S3139C3ConventionRegionTransferActual.lean", status := "CONSTRUCTED" },
    { indexId := "INDEX.FT.route-composition",
      declarations := [ "firstTriangleRouteComposition", "FirstTriangleRouteResidual" ],
      file := "S3139FirstTriangleRouteCompositionActual.lean", status := "CONSTRUCTED (conditional)" },
    { indexId := "INDEX.FT.route-conclusion",
      declarations := [ "firstTriangleRouteConclusion" ],
      file := "S3139FirstTriangleRouteConclusionActual.lean", status := "CONSTRUCTED (conditional)" },
    { indexId := "INDEX.TOOL.piTensorEntryPermute",
      declarations := [ "piTensorEntryPermute", "piTensorEntryPermute_tprod" ],
      file := "S3139ToolsPiTensorEntryPermute.lean", status := "CITABLE" },
    { indexId := "INDEX.TOOL.vendorAdapted.LGP-scalar-log-volume",
      declarations := [ "sourceLGP_linearReadout_action" ],
      file := "S3139TensorPacketScalarLogVolumeActual.lean", status := "CONSTRUCTED" },
    { indexId := "INDEX.TOOL.vendorAdapted.multiradial-procession-consumer",
      declarations := [ "SourceMultiradialProcessionConsumer",
        "sourceMultiradialProcessionConsumer",
        "sourceMultiradialProcessionConsumer_qSigned" ],
      file := "S3139MultiradialProcessionConsumerActual.lean", status := "CONSTRUCTED" } ]


/-- The open route residuals (exact names/owners), including mainline's
comparison-invariance hypothesis FT.route.comparison-invariance. -/
def routeOpenResiduals : List (String × String) :=
  [ ("FT.route.comparison-invariance",
      "S3131RouteComparisonInvarianceHypothesis (W) (phi := comparison) := forall S, W.logVolume (phi '' S) = W.logVolume S; owner mainline (FINAL-STATUS A22)"),
    ("FT.route.measure-invariance", "S3135ComparisonMeasureInvariance (abc wording): Haar/log-volume of the C3 automorphism image = volume; equivalent residual form of FT.route.comparison-invariance (paper III Prop 3.9(i)/Remark 3.9.5(i) normalization input)"),
    ("FT.M0.same-C", "same-C identification F ~ F_mod; owner mainline R1"),
    ("FT.M1.place-selection", "S3133M1ContractSeparatedMissing / S3133M1Remaining + capsule-label link; owner qpilot"),
    ("FT.stage4.unit-map", "S3136LGPGlobalUnitsToLocalUnitsActual.lgpGlobalUnitsToLocalUnits; owner stage4"),
    ("FT.fourth-triangle.inputs", "signed Theta-hull value + (xi-f) inclusion; owner shehdd route") ]

end LeanFormal.IUT.XiFPaper.S3139RouteRegistryIdsActual
