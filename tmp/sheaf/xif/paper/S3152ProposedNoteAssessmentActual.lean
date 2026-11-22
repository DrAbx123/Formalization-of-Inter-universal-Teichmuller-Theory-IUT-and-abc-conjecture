import LeanFormal.IUT.Audit.Status

/-! # S3152: assessment of qpilot's proposed narrow registry note

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Proposed note phrases and audit assessment. -/
def S3152ProposedNoteAssessment : List (String × String) := [
  ("'model-route: M0/M3 proved'", "SUPPORTED (existing proved citations)"),
  ("'M1 constructed in-model (explicit placeToMod datum)'", "SUPPORTED (PASS, CITABLE)"),
  ("'M2b definitional in-model (qVFamily := model q)'", "SUPPORTED (PASS, CITABLE)"),
  ("'F4.a/F4.b by construction'", "SUPPORTED: S3135F4BothByConstructionActual CITABLE derives the F4 clause from the two class-B data (conditional by design; model supplies them definitionally)"),
  ("'remaining model inputs: index-dependent theater family + clause slot providers'", "CONFIRMED: (i) theater family, (ii) clause-slot providers, (iii) bundled source wiring remain; full R1 composition NOT yet discharged (PARTIAL)") ]

theorem S3152ProposedNoteAssessment_length : S3152ProposedNoteAssessment.length = 5 := rfl

/-- Proposed-note assessment record. -/
def S3152ProposedNoteAssessmentRecord : Obligation :=
  { id := "IUT.project.third-reopen-proposed-note-assessment"
    source := "qpilot proposed registry note; third-reopen checklist audit"
    status := VerificationStatus.interface
    note :=
      "PROPOSED NOTE CANNOT BE ACCEPTED AS-IS: M0/M3/M1/M2b clauses are supported and CITABLE, "
      ++ "but 'F4.a/F4.b by construction' lacks formal in-model evidence, and the proposal itself "
      ++ "admits remaining theater-family/clause-provider model inputs (so R1 composition is not "
      ++ "discharged). Required: either supply the missing formal lemmas/constructions, or word "
      ++ "the note as a PARTIAL model-route status (not a closure). No reopen until Lead reviews "
      ++ "the audited evidence."
    dependsOn := [ "S3152ThirdReopenEvidenceAudit", "S3152GapsList" ] }

#check S3152ProposedNoteAssessmentRecord
#check S3152ProposedNoteAssessment_length

end LeanFormal.IUT.Audit
