import LeanFormal.IUT.Audit.Status

/-! # S3131 vendor-repo survey assets (data only; vendor = source reference, not importable) -/

namespace LeanFormal.IUT.XiFPaper.S3131VendorSurveyDataActual

def S3131VendorSurveyAssets : List (String × String) :=
  [ ("vendor/.../Iut/Stage1/CorollarySchema.lean:31-47", "PilotSide, signedPilotLogVolume, Corollary312Inequality, corollary312_of_signed_le"),
    ("CorollarySchema.lean:55-59", "structure Corollary312ComparisonData {thetaSigned, qSigned, q_positive, qSigned_le_thetaSigned}"),
    ("CorollarySchema.lean:63-83", "Corollary312ComparisonData.thetaPilot/qPilot/thetaPilot_side/qPilot_side/qPilot_positive/corollary312"),
    ("CorollarySchema.lean:85-127", "stage1Comparison + publicAudit (stage1/pilot correspondence)"),
    ("Iut/Stage1/IUTStage1IUTIVAlgebra.lean:1956-1961,2114-2144", "hullSystem.logVolume of logUnits/shiftedTensor/tensorContainer regions; normalized hull logVolume"),
    ("Iut/SourceTrace/IUTIVPaperLedger.lean:176", "GenEll transfer is an explicit hypothesis (honesty ledger)"),
    ("Iut/SourceTrace/Corollary312SourceGraph.lean:126,162,223", "qPilotAnalyticAcceptance + CorridorAcceptance records") ]

theorem S3131VendorSurveyAssets_length : S3131VendorSurveyAssets.length = 7 := rfl

#check S3131VendorSurveyAssets

end LeanFormal.IUT.XiFPaper.S3131VendorSurveyDataActual