import LeanFormal.IUT.Audit.Status

/-! # S3145: CorollarySchema vendor survey (paper-route reuse data)

Verified file:line rows from the promachina vendor snapshot for the Cor 3.12
comparison-data template (SOURCE REFERENCE ONLY - separate lake project).  No
sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (file, line, item) rows. -/
def S3145CorollarySchemaItems : List (String × Nat × String) := [
  ("Iut/Stage1/CorollarySchema.lean", 28, "signedPilotLogVolume (side, signedValue); value = -signedValue (32/37)"),
  ("Iut/Stage1/CorollarySchema.lean", 43, "Corollary312Inequality (signed theta vs signed q PilotLogVolume)"),
  ("Iut/Stage1/CorollarySchema.lean", 55, "structure Corollary312ComparisonData (thetaSigned, qSigned)"),
  ("Iut/Stage1/CorollarySchema.lean", 63, "Corollary312ComparisonData.thetaPilot"),
  ("Iut/Stage1/CorollarySchema.lean", 66, "Corollary312ComparisonData.qPilot"),
  ("Iut/Stage1/CorollarySchema.lean", 69, "thetaPilot_side"),
  ("Iut/Stage1/CorollarySchema.lean", 73, "qPilot_side"),
  ("Iut/Stage1/CorollarySchema.lean", 0, "qPilot_positive (later range in file)") ]

theorem S3145CorollarySchemaItems_length : S3145CorollarySchemaItems.length = 8 := rfl

/-- CorollarySchema survey record. -/
def S3145CorollarySchemaSurvey : Obligation :=
  { id := "IUT.project.vendor-corollary-schema-survey"
    source := "vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039/Iut/Stage1/CorollarySchema.lean"
    status := VerificationStatus.interface
    note :=
      "PAPER-ROUTE TEMPLATE FOUND (source reference only, NOT imported): signed PilotLogVolume "
      ++ "with side/value projections, Corollary312Inequality, Corollary312ComparisonData with "
      ++ "thetaPilot/qPilot(+_side/positivity). Reusable shape for a mainline Cor 3.12 "
      ++ "comparison-data record; adapt/copy definitions, never claim vendor imports."
    dependsOn := [] }

#check S3145CorollarySchemaSurvey
#check S3145CorollarySchemaItems_length

end LeanFormal.IUT.Audit
