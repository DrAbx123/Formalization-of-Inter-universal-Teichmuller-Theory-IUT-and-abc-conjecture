import LeanFormal.IUT.Audit.Status

/-! # S3137: INDEX batch-H notes — Theta V-form erratum, hull batch4, stepxi batch3

(registry frozen 14041 (third combined reopen: Option-B model-route closure); index note only; mainline/shehdd handle the single reopen)
-/

namespace LeanFormal.IUT.XiFPaper.S3137IndexBatchHNotesActual

/-- Theta-side V-form erratum: hard residual replaced by reduced sharp nodes. -/
def S3137ThetaVFormErratum : List (String × String) :=
  [ ("old-id", "MissingConcreteVFormCanonicalReadout (hard residual)"),
    ("erratum", "RECLASSIFIED: Theta-side V-form identity is now elementary Haar-scaling + rooted scaling data, not a hard residual. Old id kept as erratum alias."),
    ("new-node", "ThetaSide.vform-scaling-reduction -> S3132VFormScalingReductionActual: RootedScalingDecomposition, canonicalReadout_eq_weighted_scaling, ReducedVFormResidual, vformCanonical_of_reducedResidual (EXIT0 155510, probe 155698, checker CITABLE)"),
    ("sharp-residual", "concrete rooted scaling data (R1+R2); classification elementary/decomposable (class A/B)") ]

/-- hull batch4 ids. -/
def S3137HullBatch4Ids : List (String × String) :=
  [ ("ThetaSide.vform-scaling-reduction", "S3132VFormScalingReductionActual 155510/probe 155698"),
    ("ThetaSide.sharp-residual", "S3132ThetaSideSharpResidualActual 155003 (ThetaSideSharpResidual, thetaSideSharpResidual_canonicalReadout)"),
    ("ThetaSide.subsingleton-comparison", "S3132ThetaSideSubsingletonComparisonActual 154843 (clauseThetaValue_of_subsingleton, clauseComparisonData_thetaPilot_value_eq_weight)"),
    ("ThetaSide.composition-ledger", "S3132ThetaSideCompositionLedgerActual 155227 (composition_thetaSide)"),
    ("ThetaSide.audit-record", "S3132ThetaSideAuditRecordActual 154753 (adapted-source catalog incl GenEll Thm 2.1, audit verdict, flags)"),
    ("ThetaSide.dependency-map", "S3132ThetaSideDependencyMapActual 154746 (N0-N8)") ]

/-- stepxi batch3 ids. -/
def S3137StepxiBatch3Ids : List (String × String) :=
  [ ("INDEX.FT.C3.convention-v2-neutral-region", "S3139ComparisonRegionV2NeutralActual.SourceV2ComparisonRegion + mem_transfer/ofNeutral"),
    ("INDEX.FT.route.comparison-invariance", "S3139RouteComparisonInvarianceActual.SourceRouteComparisonInvariance + volume_image/region_volume; S3139ComparisonMeasureInvarianceResidualActual.S3135ComparisonMeasureInvariance; consumer S3139RouteComparisonInvarianceConsumerActual.sourceV2ComparisonRegion_volume_neutral"),
    ("INDEX.FT.route-named-residuals", "S3139RouteResidualQpilotNamedActual (SourceM1QpilotResidual, firstTriangleRouteComposition_of_qpilotM1) / S3139RouteResidualMainlineM0NamedActual (SourceM0MainlineResidual, firstTriangleRouteComposition_of_mainlineM0)"),
    ("INDEX.TOOL.vendorAdapted.label-averaged-log-volume", "S3139VendorLabelAveragedLogVolumeActual"),
    ("INDEX.TOOL.vendorAdapted.normalized-scaled-log-volume", "S3139VendorProcessionNormalizedLogVolumeActual"),
    ("data", "S3139VendorSurveyPart2Actual.vendorSurveyPart2; S3139V2ResidualListActual.v2RouteResiduals; S3139RouteRegistryIdsActual.routeOpenResiduals; S3139RouteIntegrationChecklistUpdatedActual.routeIntegrationChecklist") ]

end LeanFormal.IUT.XiFPaper.S3137IndexBatchHNotesActual

namespace LeanFormal.IUT.Audit

/-- INDEX: Theta V-form erratum record. -/
def INDEX_THETA_VFORM_ERRATUM : Obligation :=
  { id := "INDEX.ThetaSide.vform-scaling-reduction"
    source := "hull S3132VFormScalingReductionActual (155510/probe 155698, CITABLE); S3132ThetaSideSharpResidualActual; S3132ThetaSideSubsingletonComparisonActual"
    status := VerificationStatus.interface
    note := "ERRATUM: old hard residual MissingConcreteVFormCanonicalReadout reclassified elementary/decomposable (class A/B): ThetaSide.vform-scaling-reduction = S3132VFormScalingReductionActual (RootedScalingDecomposition, canonicalReadout_eq_weighted_scaling, ReducedVFormResidual, vformCanonical_of_reducedResidual); sharp residual = concrete rooted scaling data (R1+R2). Old id kept as erratum alias. hull batch4 ids (sharp-residual/subsingleton-comparison/composition-ledger/audit-record/dependency-map N0-N8) recorded in S3137HullBatch4Ids. Registry frozen 14041 (third combined reopen: Option-B model-route closure)."
    dependsOn := ["S3137IndexBatchHNotesActual", "S3132VFormScalingReductionActual"] }

/-- INDEX: batch-H notes record (theta erratum + hull batch4 + stepxi batch3). -/
def S3137IndexBatchHRecord : Obligation :=
  { id := "S3137.index.batch-h-notes"
    source := "hull message batch4; stepxi batch3; Lead Theta-form erratum"
    status := VerificationStatus.interface
    note := "RECORDED: Theta V-form erratum (old MissingConcreteVFormCanonicalReadout -> reduced sharp nodes, class A/B); hull batch4 ids (vform-scaling-reduction/sharp-residual/subsingleton-comparison/composition-ledger/audit-record/dependency-map N0-N8); stepxi batch3 ids (convention-v2-neutral-region, route comparison-invariance/measure-invariance, route named residuals qpilot-M1/mainline-M0, vendorAdapted label-averaged/normalized-scaled log volume, vendor survey part2). All files checker CITABLE per sources. No registry edit."
    dependsOn := ["S3137IndexBatchHNotesActual"] }

end LeanFormal.IUT.Audit