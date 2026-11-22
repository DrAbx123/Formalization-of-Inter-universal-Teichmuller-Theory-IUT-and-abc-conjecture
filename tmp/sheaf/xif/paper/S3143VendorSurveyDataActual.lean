import LeanFormal.IUT.Audit.Status

/-! # S3143: vendor treasure survey data (source-reference record)

Verified survey rows for the promachina vendor snapshot (SEPARATE lake project;
source reference only, never imported).  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (vendor file, line, names found) rows. -/
def S3143VendorSurvey : List (String × Nat × String) := [
  ("Iut/Stage1/CorollarySchema.lean", 28, "signedPilotLogVolume; PilotLogVolume.value = -signedValue (32/37)"),
  ("Iut/Stage1/CorollarySchema.lean", 43, "Corollary312Inequality (signed theta vs q PilotLogVolume)"),
  ("Iut/Stage1/CorollarySchema.lean", 55, "Corollary312ComparisonData; thetaPilot (63) qPilot (66) thetaPilot_side (69) qPilot_side (73)"),
  ("Iut/Stage1/IUTStage1IUTIVAlgebra.lean", 8092, "function-level IUT IV / GenEll relation"),
  ("Iut/Stage1/IUTStage1IUTIVAlgebra.lean", 9884, "explicit-hypothesis record; genEll_transfer field (9900); consumer 9919"),
  ("Iut/Stage1/IUTStage1FrobenioidShift.lean", 19363, "qPilotRegion; subset fields 19365/19440; choice lemma 19379-19381"),
  ("Iut/SourceTrace/Corollary312SourceGraph.lean", 47, "sourceHypothesis premise records (47/293/445); corollary312Acceptance (184)"),
  ("Iut/SourceTrace/IUTIVPaperLedger.lean", 1, "GenEll explicit-hypothesis ledger"),
  ("Iut/Stage1/IUTSourceScaffold.lean", 61, "alternate Corollary312ComparisonData scaffold") ]

theorem S3143VendorSurvey_length : S3143VendorSurvey.length = 9 := rfl

/-- Vendor survey record (source reference only). -/
def S3143VendorSurveyRecord : Obligation :=
  { id := "IUT.project.vendor-treasure-survey"
    source :=
      "vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039 " ++
        "(SEPARATE lake project; source reference only); coord/TOOL-INVENTORY.md H"
    status := VerificationStatus.interface
    note :=
      "SURVEYED (file:line verified): CorollarySchema PilotLogVolume/signedPilotLogVolume/" ++
        "Corollary312Inequality/Corollary312ComparisonData/thetaPilot/qPilot(+_side); " ++
        "IUTIVAlgebra GenEll function-level relation + explicit-hypothesis ledger record " ++
        "(genEll_transfer); FrobenioidShift qPilotRegion; SourceTrace Corollary312SourceGraph " ++
        "sourceHypothesis premises + acceptance; IUTSourceScaffold Corollary312ComparisonData " ++
        "scaffold. USE POLICY: source reference only (adapt/copy definitions); NEVER claim " ++
        "vendor imports (separate lake project; our Iut root is a different library)."
    dependsOn := [] }

#check S3143VendorSurveyRecord
#check S3143VendorSurvey_length

end LeanFormal.IUT.Audit
