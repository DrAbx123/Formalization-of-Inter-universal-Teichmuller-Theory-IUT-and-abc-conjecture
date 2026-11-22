import LeanFormal.IUT.Audit.Status

/-! # S3137: hull ThetaSide paper-route ids note (registry frozen; index note)

hull-provided citable ids (all checker CITABLE, probe trio):
* INDEX.TOOL/ThetaSide.haar-integration -> S3132ThetaSideHaarIntegrationActual (thetaSideConcreteMu, thetaSideConcreteMu_isAddHaar, thetaSideResidual_iff_identity) 153668;
* INDEX.TOOL/ThetaSide.residual-spec -> S3132ThetaSideDataResidualSpecActual (ThetaSideNativeDataResidual, thetaSideNativeData_of_residual) 152549;
* INDEX.TOOL/ThetaSide.canonical-subsingleton -> S3132ThetaSideCanonicalSubsingletonActual (canonicalRootedHC_of_subsingleton) 153313;
* INDEX.ThetaSide.conditional-readout -> S3132ThetaSideCanonicalConditionalActual (thetaSideCanonicalReadout_conditional, thetaSideRawLogVolume_conditional) 153407;
* INDEX.ThetaSide.clause-residual -> S3132ThetaSideClauseResidualActual (ClauseSideVFormResidual, clauseRawLogVolume_eq_canonical, clauseCanonicalReadout) 154429;
* INDEX.ThetaSide.model-clause-residual -> S3132ThetaSideModelClauseResidualActual (ModelSideVFormResidual, modelCanonicalReadout) 154414;
* INDEX.ThetaSide.comparison-data -> S3132ThetaSideClauseComparisonDataActual + S3132ThetaSideModelComparisonDataActual (clauseComparisonData/modelComparisonData, thetaPilot.value = canonical readout, corollary312) 154501/154516;
* INDEX.SOURCE.adapted-vendor -> S3132SourceAdaptedPilotComparisonActual 154038, S3132SourceAdaptedCorollary312DataActual 154051, S3132IVGenEllShadowAdapterActual 153924, S3132ThetaSideSurveyRecordActual 153556 (vendor promachina adaptations with attribution);
* INDEX.ThetaSide.milestone -> S3132ThetaSideMilestoneRecordActual 152675 + S3132ThetaSideMilestoneBRecordActual 154345 (pins 14041/23066/15501).
Remaining residual: LGPModelSourceClauseMissing + MissingConcreteVFormCanonicalReadout.
-/

namespace LeanFormal.IUT.Audit

/-- hull ThetaSide ids for next re-pin (data). -/
def S3137HullThetaSideIds : List (String × String) :=
  [ ("INDEX.TOOL/ThetaSide.haar-integration", "S3132ThetaSideHaarIntegrationActual (153668)"),
    ("INDEX.TOOL/ThetaSide.residual-spec", "S3132ThetaSideDataResidualSpecActual (152549)"),
    ("INDEX.TOOL/ThetaSide.canonical-subsingleton", "S3132ThetaSideCanonicalSubsingletonActual (153313)"),
    ("INDEX.ThetaSide.conditional-readout", "S3132ThetaSideCanonicalConditionalActual (153407)"),
    ("INDEX.ThetaSide.clause-residual", "S3132ThetaSideClauseResidualActual (154429)"),
    ("INDEX.ThetaSide.model-clause-residual", "S3132ThetaSideModelClauseResidualActual (154414)"),
    ("INDEX.ThetaSide.comparison-data", "S3132ThetaSideClauseComparisonDataActual + S3132ThetaSideModelComparisonDataActual (154501/154516)"),
    ("INDEX.SOURCE.adapted-vendor", "S3132SourceAdaptedPilotComparisonActual 154038, S3132SourceAdaptedCorollary312DataActual 154051, S3132IVGenEllShadowAdapterActual 153924, S3132ThetaSideSurveyRecordActual 153556"),
    ("INDEX.ThetaSide.milestone", "S3132ThetaSideMilestoneRecordActual 152675 + S3132ThetaSideMilestoneBRecordActual 154345") ]

/-- INDEX record: hull ThetaSide ids. -/
def S3137HullThetaSideBatchRecord : Obligation :=
  { id := "S3137.index.hull-theta-side-ids-batch"
    source := "hull message; S3132ThetaSide* files; pins 14041/23066/15501"
    status := VerificationStatus.interface
    note := "HULL THETA-SIDE IDS (all checker CITABLE, probe trio): haar-integration/residual-spec/canonical-subsingleton/conditional-readout/clause-residual/model-clause-residual/comparison-data/adapted-vendor/milestone. Vendor promachina adaptations with attribution. Remaining ThetaSide residual: LGPModelSourceClauseMissing + MissingConcreteVFormCanonicalReadout. Registry frozen; data note only."
    dependsOn := ["S3137HullThetaSideIdsNoteActual"] }

end LeanFormal.IUT.Audit