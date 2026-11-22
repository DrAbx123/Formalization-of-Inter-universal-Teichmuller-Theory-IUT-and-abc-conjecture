import LeanFormal.IUT.Audit.Status

/-! # S3141: watch-status data for residual candidates

Data rows of the current watch list (owner, status class, next action).  No
sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (candidate, owner, status, next action) rows. -/
def S3141WatchStatus : List (String × String × String × String) := [
  ("R1.M2a", "qpilot", "OPEN", "real EXIT=0 file with declarations + trio probe closing valued_coe_rat"),
  ("F4.b.nontrivial-scaling", "abc", "OPEN (A13 structural)", "task-72 model design: genuine unit group, symmetric O != hull, explicit nontrivial z"),
  ("F4.a compatibility", "abc/task-72", "REDUCTION", "new source datum; only model closure via task-72 (A12)"),
  ("M1 bad-tensor-index", "qpilot/lattice", "OPEN", "bad<->C3 equivalence + base-place equality; concrete donor tool green (probe red)"),
  ("GATE V4", "abc/mainline", "NOT PROMOTED", "separate circularity + input-fidelity audit required before any promotion"),
  ("Index 52/47", "lattice", "DATA-ONLY", "not gate imports; no reopen effect") ]

theorem S3141WatchStatus_length :
    S3141WatchStatus.length = 6 := rfl

/-- Watch-status record. -/
def S3141WatchStatusRecord : Obligation :=
  { id := "IUT.project.watch-status"
    source :=
      "registry 13108 frozen; task-72 reports; M2a/M1 candidate scans; GATE V4 status"
    status := VerificationStatus.interface
    note :=
      "WATCH LIST (no reopen unless a REAL closure appears): M2a OPEN (real file " ++
        "EXIT=1 pending; doc-only does not count), F4.b nontrivial scaling OPEN under " ++
        "A13 structural forcing (task-72 model design only), F4.a is a REDUCTION " ++
        "(A12 new source datum), M1 OPEN (bad<->C3 + base-place equality; concrete " ++
        "donor tool green but probe red), GATE V4 NOT PROMOTED (separate audit needed), " ++
        "lattice INDEX 52/47 data-only (no reopen effect)."
    dependsOn := [ "S3140FinalAcceptanceRecordActual" ] }

#check S3141WatchStatusRecord
#check S3141WatchStatus_length

end LeanFormal.IUT.Audit
