import LeanFormal.IUT.Audit.Status

/-! # S3141: second-reopen checklist (M2a / F4(b) model closures)

Data + procedure record for the TWO currently-likely second reopen triggers.
Registry is frozen at 13108; a second combined reopen is allowed ONLY after a
REAL residual closure with the evidence below.  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Evidence requirements before M2a may be reopened as CLOSED. -/
def S3141M2aReopenRequirements : List String := [
  "real EXIT=0 file with ACTUAL declarations closing the valued_coe_rat presentation bridge (doc-only files do NOT count)",
  "trio / no-sorry axiom probe on the closing declarations",
  "tools/xif_citable_check.ps1 verdict CITABLE",
  "registry note update M2a CLOSED and R1 = M1 + M2b ONLY after the evidence",
  "single combined reopen + single gate re-pin (no other registry edits)" ]

theorem S3141M2aReopenRequirements_length :
    S3141M2aReopenRequirements.length = 5 := rfl

/-- Evidence requirements before an F4(b) nontrivial-scaling MODEL closure may be reopened. -/
def S3141F4bModelReopenRequirements : List String := [
  "task-72 from-scratch model with a genuine value-monoid unit group, symmetric O != hull, explicit nontrivial z != 1",
  "S3135CompletionBaseFieldUnitScalar z PROVED for that model",
  "S3135ScalingLogDegreeZero proved NON-definitionally (via multiplicativity/log-degree, not scaling := 1)",
  "closure documented as a MODEL object (not the frozen tree claim, not general)",
  "trio probe + CITABLE + no concrete-only leakage into the general claims" ]

theorem S3141F4bModelReopenRequirements_length :
    S3141F4bModelReopenRequirements.length = 5 := rfl

/-- Second-reopen checklist record (procedure + trigger conditions). -/
def S3141SecondReopenChecklist : Obligation :=
  { id := "IUT.project.second-reopen-checklist"
    source :=
      "Lead §7.8 policy; registry frozen 13108; combined-reopen checklist " ++
        "coord/COMBINED-REOPEN-CHECKLIST.md; C3 closure template (first reopen)"
    status := VerificationStatus.interface
    note :=
      "SECOND REOPEN (deferred until a REAL closure): TWO likely triggers are " ++
        "M2a (valued_coe_rat presentation bridge) and an F4(b) nontrivial-scaling " ++
        "MODEL closure from task-72. Evidence gate for either: EXIT=0 file with " ++
        "ACTUAL declarations + trio/no-sorry probe + xif_citable_check CITABLE; " ++
        "for F4(b) the scaling log-degree must be derived non-definitionally and " ++
        "the closure documented as a MODEL object (no general/frozen-tree overclaim, " ++
        "A13 structural forcing acknowledged). Then ONE combined reopen (registry " ++
        "note only) + ONE gate re-pin + record/index/ledger update. No v4 promotion."
    dependsOn :=
      [ "S3140FinalAcceptanceRecordActual", "S3140ClosureGateActual" ] }

#check S3141SecondReopenChecklist
#check S3141M2aReopenRequirements_length
#check S3141F4bModelReopenRequirements_length

end LeanFormal.IUT.Audit
