import LeanFormal.IUT.Audit.Status

/-! # S3153: F4.a/F4.b by-construction evidence data (corrected audit item d)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Evidence rows for checklist item (d). -/
def S3153F4BothEvidence : List (String × String × String) := [
  ("S3135F4BothByConstructionActual.lean", "EXIT=0, CITABLE (1 decl)", "theorem s3135_actualF4_of_realifiedIdent_and_processionDatum : from hid : S3135ValueMonoidRealifiedIdentification and hd : S3135ProcessionScalingUnitDatum derives FrontierHeightComparisonClause (the actual F4 clause)"),
  ("S3135RealifiedIdentificationActual.lean", "EXIT=0 green", "def S3135ValueMonoidRealifiedIdentification (class-B data) + theorem s3135_compatibility_of_realifiedIdentification"),
  ("S3135ProcessionUnitDatumActual.lean", "EXIT=0 green", "structure S3135ProcessionScalingUnitDatum (class-B data) + theorem s3135_procession_scaling_unit_degree_zero"),
  ("S3135ModelF4aTemplateActual.lean", "EXIT=0 green", "model F4.a template"),
  ("audit note", "conditional by design", "the F4 clause is derived FROM the two class-B data; in the from-scratch model both are definitional/choice, so (d) PASS with that qualification") ]

theorem S3153F4BothEvidence_length : S3153F4BothEvidence.length = 5 := rfl

/-- F4 both-by-construction evidence record. -/
def S3153F4BothEvidenceRecord : Obligation :=
  { id := "IUT.project.f4-both-by-construction-evidence"
    source := "Lead checker verification; abc batch 2026-11-10 04:51; xif_citable_check"
    status := VerificationStatus.interface
    note :=
      "ITEM (d) PASS: S3135F4BothByConstructionActual (CITABLE) derives the actual F4 clause from "
      ++ "the two class-B data (S3135ValueMonoidRealifiedIdentification + S3135ProcessionScaling"
      ++ "UnitDatum) via normalizedRealifiedPrimePowerHom_degree and "
      ++ "s3135_procession_scaling_unit_degree_zero; supporting files green. Conditional on the "
      ++ "two class-B data BY DESIGN (model supplies them definitionally). Corrects the earlier "
      ++ "batch-L GAP verdict (abc evidence landed after the draft)."
    dependsOn := [ "S3135F4BothByConstructionActual", "S3135RealifiedIdentificationActual",
        "S3135ProcessionUnitDatumActual" ] }

#check S3153F4BothEvidenceRecord
#check S3153F4BothEvidence_length

end LeanFormal.IUT.Audit
