import LeanFormal.IUT.Audit.Status

/-! # S3142: M2a reopening watch data (evidence discipline)

Status rows and the false-green history for M2a.  M2a stays OPEN.  No
sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (M2a observation, status, note) rows. -/
def S3142M2aWatch : List (String × String × String) := [
  ("S3133M2aClosedActual.lean 147613/SIZE 2578", "DOC-ONLY FALSE GREEN", "0 declarations; NOT a closure; counted closed once by mistake"),
  ("S3133M2aClosedActual.lean current", "EXIT=1", "real-declaration attempt pending fix; not citable"),
  ("S3137M2aBridgeMissingActual.lean", "EXIT=1", "bridge-missing spec attempt pending"),
  ("R1.M2a residual", "OPEN", "valued_coe_rat presentation bridge remains the exact missing"),
  ("reopen requirement", "CHECKLIST", "real EXIT=0 file with declarations + trio probe + CITABLE; then ONE combined reopen") ]

theorem S3142M2aWatch_length : S3142M2aWatch.length = 5 := rfl

/-- M2a watch record. -/
def S3142M2aWatchRecord : Obligation :=
  { id := "IUT.project.m2a-watch"
    source := "audit of S3133M2aClosedActual / S3137M2aBridgeMissingActual; ledger false-green entry"
    status := VerificationStatus.interface
    note :=
      "M2a REMAINS OPEN: the 147613 doc-only file was a false green and must never be " ++
        "counted; the real-declaration attempts are currently EXIT=1. Reopen requires a " ++
        "real EXIT=0 file with ACTUAL declarations, trio/no-sorry probe, and " ++
        "xif_citable_check CITABLE; then R1 = M1 + M2b with ONE combined reopen."
    dependsOn := [ "S3133M2aClosedActual", "S3131FinalResidualRegistryActual" ] }

#check S3142M2aWatchRecord
#check S3142M2aWatch_length

end LeanFormal.IUT.Audit
