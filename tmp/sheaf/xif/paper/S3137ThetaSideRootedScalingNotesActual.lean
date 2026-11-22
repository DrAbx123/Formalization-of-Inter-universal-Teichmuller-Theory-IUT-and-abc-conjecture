import LeanFormal.IUT.Audit.Status

/-! # S3137: ThetaSide rooted-scaling / weighted-rooted-identity index notes (hull batch)

hull-provided citable entries (checker JSONs, probe trio 160963-160977):
- ThetaSide.rooted-scaling-R1 -> S3132RootedScalingDataTrivialActual 159097
  (RootedScalingDecomposition, logExpScalar, reducedResidual_iff_weightedIdentity,
  WeightedRootedIdentity, vformCanonical_of_weightedIdentity);
- ThetaSide.rooted-scaling-formula -> S3132RootedScalingDataFormulaActual 160816
  (paperFormulaScalar, paperRootThetaFormulaLog_eq_log_paperFormulaScalar,
  rootedScalingDecomposition_of_paperGap; explicit data hypothesis hc);
- ThetaSide.sharp-residual-reduced -> S3132ThetaSideSharpResidualReducedActual 159585
  (sharpResidual_iff_weightedIdentity, ModelWeightedRootedIdentity);
- ThetaSide.comparison-region-bundle -> S3132ThetaSideComparisonRegionBundleActual 160737;
- ThetaSide.inventory-13-slot -> S3132ThetaSideInventory13SlotActual 156686;
- SOURCE.iut4-section1-survey -> S3132IVSection1SurveyRecordActual 156692
  (negative UndilatedHeightBound).
ERRATUM REFINEMENT (supersedes the earlier ThetaSide.vform-scaling-reduction note):
REPLACE the hard 'vform-canonical residual' node by
ThetaSide.weighted-rooted-identity (R2), with ThetaSide.rooted-scaling-R1 as
eliminated/content-free; keep the old MissingConcreteVFormCanonicalReadout id as
erratum alias.  Prior art (frozen obstacles): CertificateHullWiring:106/99/155/204/272/347,
CertificateHullWiringRealization:48-129, CardAMPLThetaBoundSupply:78/94/116/125,
CardQCMPComparison:50-68.  Pin: registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.S3137ThetaSideRootedScalingNotesActual

/-- hull rooted-scaling index entries (data). -/
def S3137ThetaSideRootedScalingIds : List (String × String) :=
  [ ("ThetaSide.rooted-scaling-R1", "S3132RootedScalingDataTrivialActual 159097 (RootedScalingDecomposition, logExpScalar, reducedResidual_iff_weightedIdentity, WeightedRootedIdentity, vformCanonical_of_weightedIdentity) — eliminated/content-free"),
    ("ThetaSide.rooted-scaling-formula", "S3132RootedScalingDataFormulaActual 160816 (paperFormulaScalar, paperRootThetaFormulaLog_eq_log_paperFormulaScalar, rootedScalingDecomposition_of_paperGap; explicit data hypothesis hc)"),
    ("ThetaSide.sharp-residual-reduced", "S3132ThetaSideSharpResidualReducedActual 159585 (sharpResidual_iff_weightedIdentity, ModelWeightedRootedIdentity)"),
    ("ThetaSide.weighted-rooted-identity", "R2: ThetaSide.sharp-residual-reduced + ThetaSide.rooted-scaling-R1/rooted-scaling-formula; replaces hard vform-canonical residual"),
    ("ThetaSide.comparison-region-bundle", "S3132ThetaSideComparisonRegionBundleActual 160737"),
    ("ThetaSide.inventory-13-slot", "S3132ThetaSideInventory13SlotActual 156686"),
    ("SOURCE.iut4-section1-survey", "S3132IVSection1SurveyRecordActual 156692 (negative UndilatedHeightBound)"),
    ("prior-art frozen obstacles", "CertificateHullWiring:106/99/155/204/272/347; CertificateHullWiringRealization:48-129; CardAMPLThetaBoundSupply:78/94/116/125; CardQCMPComparison:50-68"),
    ("ThetaSide.h3-correction", "S3132RootedCoefficientCorrectionActual 162986 (H3 e=1 correction)"),
    ("ThetaSide.h4-slot", "S3132ThetaSideHullSlotWiringActual 161243 (H4 hull<=theta slot)"),
    ("ThetaSide.h5-slot", "S3132ThetaSideQSideSlotWiringActual 161517 (H5 q-side signed comparison slot)"),
    ("ThetaSide.cert-signed", "S3132ThetaSideCertificateSignedShapeActual 161511"),
    ("ThetaSide.bundle-v2", "S3132ThetaSideComparisonRegionBundleV2Actual 163220"),
    ("ThetaSide.remaining-hypotheses", "S3132ThetaSideRemainingHypothesesRecordActual 161139 (H1-H6 remaining hypotheses record; pin 14041)"),
    ("ThetaSide.endgame-rows", "S3132ThetaSideEndgameRowsActual 163533 (H1-H6 corrected endgame rows; pin 14041)") ]

theorem S3137ThetaSideRootedScalingIds_length :
    S3137ThetaSideRootedScalingIds.length = 15 := rfl

end LeanFormal.IUT.XiFPaper.S3137ThetaSideRootedScalingNotesActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: ThetaSide weighted-rooted-identity erratum. -/
def INDEX_THETA_WEIGHTED_ROOTED_IDENTITY : Obligation :=
  { id := "INDEX.ThetaSide.weighted-rooted-identity"
    source := "hull S3132RootedScalingDataTrivialActual 159097; S3132RootedScalingDataFormulaActual 160816; S3132ThetaSideSharpResidualReducedActual 159585; S3132ThetaSideComparisonRegionBundleActual 160737; S3132IVSection1SurveyRecordActual 156692; prior art CertificateHullWiring/CardAMPLThetaBoundSupply/CardQCMPComparison"
    status := VerificationStatus.interface
    note := "ERRATUM/REFINEMENT (updated with hull H3-H6 execution assets): the hard 'vform-canonical residual' node is REPLACED by ThetaSide.weighted-rooted-identity (R2), with ThetaSide.rooted-scaling-R1 eliminated/content-free (RootedScalingDataTrivial: reducedResidual_iff_weightedIdentity + vformCanonical_of_weightedIdentity); ThetaSide.rooted-scaling-formula gives the explicit paper formula (paperFormulaScalar etc., data hypothesis hc); sharp residual reduced (sharpResidual_iff_weightedIdentity). Old MissingConcreteVFormCanonicalReadout id kept as erratum alias. Classification elementary/decomposable (class A/B). Frozen obstacles from prior art listed. Hull execution assets: H3 correction S3132RootedCoefficientCorrectionActual (e=1), H4 hull<=theta slot S3132ThetaSideHullSlotWiringActual, H5 q-side slot S3132ThetaSideQSideSlotWiringActual, certificate signed shape S3132ThetaSideCertificateSignedShapeActual, comparison region bundle V2 S3132ThetaSideComparisonRegionBundleV2Actual, remaining hypotheses record S3132ThetaSideRemainingHypothesesRecordActual, corrected endgame rows S3132ThetaSideEndgameRowsActual 163533 (pin 14041), all CITABLE. Pin 14041; no registry edits."
    dependsOn := ["S3137ThetaSideRootedScalingNotesActual", "S3132RootedScalingDataTrivialActual", "S3132ThetaSideSharpResidualReducedActual"] }

end LeanFormal.IUT.Audit