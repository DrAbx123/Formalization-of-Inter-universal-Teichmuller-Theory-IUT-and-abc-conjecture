import LeanFormal.IUT.Audit.Status

/-! # S3137: vendor treasure mapping — promachina CorollarySchema <-> our INDEX ids

Source reference only (vendor/promachina/snapshots/..., a separate lake project;
CANNOT be imported).  Key treasure found (file:line):

* Iut/Stage1/CorollarySchema.lean:25-47  Corollary312Inequality, signedPilotLogVolume,
  PilotSide, corollary312_of_signed_le;
* :49-59  structure Corollary312ComparisonData {thetaSigned, qSigned,
  q_positive : 0 < -qSigned, qSigned_le_thetaSigned};
* :61-83  thetaPilot, qPilot (PilotLogVolume), thetaPilot_side, qPilot_side,
  qPilot_positive, corollary312 (Corollary312Inequality thetaPilot qPilot);
* :85-104 Stage1Comparison + stage1Comparison_comparison_eq_corollary312.
* Iut/Stage1/IUTStage1FrobenioidShift.lean  qPilotRegion (many, e.g. :19564,
  :20094, :20277, :20678, :24126, ...);
* Iut/Stage1/IUTStage1IUTIVAlgebra.lean  IUT IV/GenEll function-level relations;
* Iut/SourceTrace/Corollary312SourceGraph.lean:162 qPilotAnalyticAcceptance.

Mapping to our INDEX ids:
* Corollary312Inequality / Corollary312ComparisonData / thetaPilot+qPilot
  <-> INDEX.PAPER-ROUTE.height-comparison + INDEX.PAPER-ROUTE.region-volume-weight
  (the signed comparison payload) and our S3137 qTheta bridge
  (qThetaPilotLogVolumeComparison_of_modelMap gives qSigned <= thetaSigned with
  qSigned = qPilotLogVolumeReading, thetaSigned = thetaPilotHullLogVolumeReal);
* corollary312 <-> our signed comparison theorem chain;
* qPilot_positive (0 < -qSigned) <-> our q-pilot positivity (q != 1);
* qPilotRegion / qPilotAnalyticAcceptance <-> S3131 QC/HC readouts and
  S3129/FinitePlaceIQHullInterface log-volume carriers.

Adaptation note: the vendor schema is the EXACT shape our paper-route fields
should be presented in for acceptance; the vendor record isolates the real-valued
comparison from any model/bridge, matching our INDEX.PAPER-ROUTE presentation.
Data only.  WRITE-ONLY.
-/

namespace LeanFormal.IUT.XiFPaper.S3137VendorMappingActual

/-- Vendor CorollarySchema names <-> our INDEX ids (data). -/
def S3137VendorCorollarySchemaMapping : List (String × String) :=
  [ ("Corollary312Inequality / signedPilotLogVolume", "INDEX.PAPER-ROUTE.height-comparison; S3137 qTheta bridge signed comparison"),
    ("Corollary312ComparisonData {thetaSigned, qSigned, q_positive, qSigned_le_thetaSigned}", "INDEX.PAPER-ROUTE.height-comparison + region-volume-weight; our S3137SameCModelMapResidual + qTheta comparison"),
    ("thetaPilot / qPilot (PilotLogVolume)", "S3137QThetaPilotLogVolumeReadingsActual (qPilotLogVolumeReading, thetaPilotHullLogVolume, thetaPilotHullLogVolumeReal)"),
    ("thetaPilot_side / qPilot_side", "S3137 qTheta readings side tags"),
    ("qPilot_positive (0 < -qSigned)", "q-pilot positivity: q != 1 => 0 < -qPilotLogVolumeReading"),
    ("corollary312 / corollary312_of_signed_le", "S3137 signed comparison qThetaPilotLogVolumeComparison_of_modelMap/_of_sameC"),
    ("Stage1Comparison / stage1Comparison_comparison_eq_corollary312", "INDEX.PAPER-ROUTE.bridge-package (shape match)"),
    ("qPilotRegion (IUTStage1FrobenioidShift)", "S3131 QC/HC readouts; S3129 hull carrier; FinitePlaceIQHullInterface"),
    ("qPilotAnalyticAcceptance (Corollary312SourceGraph:162)", "INDEX.PAPER-ROUTE.region-volume-weight (analytic acceptance half)") ]

/-- Vendor treasure inventory (source-only; cannot import). -/
def S3137VendorTreasureInventory : List (String × String) :=
  [ ("vendor/promachina/snapshots/1fa6387f.../Iut/Stage1/CorollarySchema.lean", "Corollary312Inequality, Corollary312ComparisonData, thetaPilot/qPilot, sides, qPilot_positive, corollary312, Stage1Comparison (lines 25-104)"),
    ("vendor/promachina/snapshots/1fa6387f.../Iut/Stage1/IUTStage1FrobenioidShift.lean", "qPilotRegion (lines 19564, 20094, 20277, 20678, 24126, ...)"),
    ("vendor/promachina/snapshots/1fa6387f.../Iut/Stage1/IUTStage1IUTIVAlgebra.lean", "IUT IV/GenEll function-level relations"),
    ("vendor/promachina/snapshots/1fa6387f.../Iut/SourceTrace/Corollary312SourceGraph.lean", "qPilotAnalyticAcceptance line 162; source graph"),
    ("vendor/promachina/snapshots/1fa6387f.../Iut/SourceTrace/IUTIVPaperLedger.lean", "GenEll explicit-hypothesis honesty"),
    ("vendor/promachina/snapshots/1fa6387f.../Iut/Stage1/IUTSourceScaffold.lean", "Corollary312ComparisonData scaffold") ]

end LeanFormal.IUT.XiFPaper.S3137VendorMappingActual

namespace LeanFormal.IUT.Audit

/-- INDEX: vendor mapping (source-only reference). -/
def INDEX_VENDOR_COR312_SCHEMA : Obligation :=
  { id := "INDEX.VENDOR.cor312-schema"
    source := "coord/TOOL-INVENTORY.md section H; vendor/promachina/snapshots/1fa6387f.../Iut/Stage1/CorollarySchema.lean:25-104; IUTStage1FrobenioidShift qPilotRegion; Corollary312SourceGraph:162"
    status := VerificationStatus.interface
    note := "SOURCE-ONLY vendor treasure (separate lake project; cannot import). Corollary312ComparisonData {thetaSigned, qSigned, q_positive : 0 < -qSigned, qSigned_le_thetaSigned} is the EXACT acceptance shape for our INDEX.PAPER-ROUTE fields; thetaPilot/qPilot map to S3137QThetaPilotLogVolumeReadingsActual; corollary312 maps to S3137 signed comparison chain; qPilot_positive maps to q != 1 positivity; qPilotRegion maps to S3131 QC/HC + S3129 hull. Full mapping data in S3137VendorCorollarySchemaMapping / S3137VendorTreasureInventory. Adaptation only (no import). Not a residual."
    dependsOn := ["S3137VendorMappingActual"] }

end LeanFormal.IUT.Audit
