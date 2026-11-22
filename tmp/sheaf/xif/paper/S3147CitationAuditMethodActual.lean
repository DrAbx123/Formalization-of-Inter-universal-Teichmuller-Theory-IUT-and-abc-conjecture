import LeanFormal.IUT.Audit.Status

/-! # S3147: citation-audit method (avoid false gap claims)

Method record for reclassifying bracketed citations; pins unchanged.  No
sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Mandatory checks for each bracketed citation. -/
def S3147CitationAuditChecks : List String := [
  "is the cited paper/text present in papers/motizuki_corpus? (corpus check)",
  "is the cited statement proved there or only stated? (proved-in-corpus => class B, not a gap)",
  "is it a definition/elementary observation? (class A)",
  "is it a convention/choice? (class C, state explicitly)",
  "only if genuinely external/difficult: class D (document why, minimal set)",
  "never label a proved-in-corpus statement a 'machine gap' or 'external paper input'" ]

theorem S3147CitationAuditChecks_length : S3147CitationAuditChecks.length = 6 := rfl

/-- Citation-audit method record. -/
def S3147CitationAuditMethod : Obligation :=
  { id := "IUT.project.citation-audit-method"
    source := "Lead citation-reclassification directive; user challenge; corpus SOURCE_TEXT_AUDIT.md"
    status := VerificationStatus.interface
    note :=
      "METHOD: for every bracketed citation, check corpus presence + proved/stated status and "
      ++ "classify A/B/C/D; class B (proved-in-corpus) is a formalization target, not a gap. No "
      ++ "false 'difficult input' labels; final reclassification table folded into the acceptance "
      ++ "appendices when mainline's table lands (doc-only; pins registry 13129/gate 23066/record "
      ++ "15501 unchanged unless a real closure triggers reopen)."
    dependsOn := [ "S3147CitationClassificationData" ] }

#check S3147CitationAuditMethod
#check S3147CitationAuditChecks_length

end LeanFormal.IUT.Audit
