import LeanFormal.IUT.Audit.Status

/-! # S3144: citable-batch registry (all audit batches)

Summary data of the audit/pins/watch batches and their citable-check verdicts.
No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (batch, file count, status) rows. -/
def S3144BatchSummary : List (String × Nat × String) := [
  ("S3141 batch A (audit/pins/watch records)", 10, "ALL EXIT=0/fresh first pass; sampled CITABLE (pins record 6 decls probe_ok)"),
  ("S3142 batch B (reopen/evidence/watch data)", 8, "ALL EXIT=0/fresh first pass; sampled CITABLE (C3 evidence 3 decls probe_ok)"),
  ("S3143 batch C (vendor survey/no-import)", 8, "ALL EXIT=0/fresh after 1 typo fix; vendor survey 3 decls probe_ok CITABLE"),
  ("S3144 batch D (closure consolidation)", 8, "written in this batch; target ALL EXIT=0/fresh") ]

theorem S3144BatchSummary_length : S3144BatchSummary.length = 4 := rfl

/-- Citable-batch registry (all). -/
def S3144CitableBatchRegistryAll : Obligation :=
  { id := "IUT.project.citable-batch-registry-all"
    source := "tools/xif_citable_check.ps1 runs on S3141/S3142/S3143 batches"
    status := VerificationStatus.interface
    note :=
      "AUDIT BATCHES A/B/C (26 files incl. probes): ALL EXIT=0 and fresh (batch C had one " ++
        "typo, fixed and re-greened). Sampled verdicts CITABLE on the pins record, C3 evidence " ++
        "bundle, vendor survey/no-import and gate receipt; batch D is the closure-consolidation " ++
        "batch. Every claim file is checked with tools/xif_citable_check.ps1."
    dependsOn := [ "S3143CitableBatchRegistry" ] }

#check S3144CitableBatchRegistryAll
#check S3144BatchSummary_length

end LeanFormal.IUT.Audit
