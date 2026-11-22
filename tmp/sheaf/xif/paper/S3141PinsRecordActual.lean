import LeanFormal.IUT.Audit.Status

/-! # S3141: pinned acceptance-artifact record (post-C3-closure reopen)

Data record of the definitive pins.  No re-pin without a real residual closure. -/

namespace LeanFormal.IUT.Audit

/-- Gate pin string: file|src_size|src_sha256|olean_sha256. -/
def S3141GatePin : String :=
  "S3140ClosureGateActual|22958|41C7ED9606DE20D80C6FFFA356B186EF70725FA6352A72C7957F02F0A778EE3D|4E8DFE7F1522AEE45775CF383123D1169E2F2AB0DA8C9AB6753F872EE76F34EE"

/-- Registry pin string: file|src_size|src_sha256|olean_mtime. -/
def S3141RegistryPin : String :=
  "S3131FinalResidualRegistryActual|13108|55012B55582EA268781F5679D496108E9781121331F9E47CB616B2D23FD55801|04:06:14"

/-- Acceptance-record pin string: file|src_size|src_sha256|olean_sha256. -/
def S3141RecordPin : String :=
  "S3140FinalAcceptanceRecordActual|14932|13C344D174B990B6D2332707415508345D873B5CE16A9EFF4C23019A89034BBA|210E27D5F8923B47F151013F8722C59A4E33B2E3DA8247276C34AA59FF1763E0"

theorem S3141GatePin_eq :
    S3141GatePin =
      "S3140ClosureGateActual|22958|41C7ED9606DE20D80C6FFFA356B186EF70725FA6352A72C7957F02F0A778EE3D|4E8DFE7F1522AEE45775CF383123D1169E2F2AB0DA8C9AB6753F872EE76F34EE" := rfl

theorem S3141RegistryPin_eq :
    S3141RegistryPin =
      "S3131FinalResidualRegistryActual|13108|55012B55582EA268781F5679D496108E9781121331F9E47CB616B2D23FD55801|04:06:14" := rfl

/-- Pins record (gate / registry / acceptance record). -/
def S3141PinsRecord : Obligation :=
  { id := "IUT.project.pins-record"
    source :=
      "post-C3-closure combined reopen: registry 13108, gate 22958, record 14932; " ++
        "AUDIT_LEDGER 04:11; coord/FINAL-ARTIFACTS-20261110.md"
    status := VerificationStatus.interface
    note :=
      "DEFINITIVE PINS (2026-11-10, after the first real residual closure): gate " ++
        "S3140ClosureGateActual EXIT=0 SIZE 22958 src 41C7ED96... olean 4E8DFE7F... " ++
        "(olean 04:08:11 > registry olean 04:06:14; 41 deps 0 stale; 53 decls = " ++
        "50 trio + 3 no-axiom, zero sorryAx); registry S3131FinalResidualRegistryActual " ++
        "frozen SIZE 13108 src 55012B55... (C3 convention CLOSED note; 15 ids/order/ABC " ++
        "unchanged); acceptance record S3140FinalAcceptanceRecordActual SIZE 14932 src " ++
        "13C344D1... olean 210E27D5... (C3 CLOSED folded, M2a OPEN, A12/A13 unchanged, " ++
        "no v4). No re-pin without a REAL residual closure; then ONE combined reopen + " ++
        "ONE re-pin."
    dependsOn :=
      [ "S3140ClosureGateActual", "S3131FinalResidualRegistryActual",
        "S3140FinalAcceptanceRecordActual" ] }

#check S3141PinsRecord
#check S3141GatePin_eq
#check S3141RegistryPin_eq

end LeanFormal.IUT.Audit
