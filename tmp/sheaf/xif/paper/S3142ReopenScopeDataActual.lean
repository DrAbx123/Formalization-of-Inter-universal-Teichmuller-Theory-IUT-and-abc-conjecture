import LeanFormal.IUT.Audit.Status

/-! # S3142: second-reopen scope data (one reopen + one re-pin)

Data rows of the allowed scope for the next combined reopen.  Registry stays
frozen until a real closure.  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (phase, scope item) rows allowed in the next combined reopen. -/
def S3142ReopenScope : List (String × String) := [
  ("registry", "ONE note edit for the real closure + audit citation; 15 ids/order/ABC unchanged; no other edits"),
  ("gate", "touch+append S3140ClosureGateActual; verify 41 deps fresh and olean mtime > registry olean"),
  ("probes", "recompile _S3140ClosureGateAxiomsProbe + _S3140FinalAxiomRecountProbeActual against the new gate"),
  ("record", "update C3/M2a/F4b status lines + pin numbers; M2a/input-fidelity wording only if evidenced"),
  ("docs", "FINAL-ARTIFACTS rows + ledger entry + combined-reopen checklist update"),
  ("policy", "ONE reopen + ONE re-pin; no v4 promotion; notify Lead/mainline/hull/lattice/abc/qpilot/stepxi") ]

theorem S3142ReopenScope_length : S3142ReopenScope.length = 6 := rfl

/-- Second-reopen scope record. -/
def S3142ReopenScopeRecord : Obligation :=
  { id := "IUT.project.second-reopen-scope"
    source := "Lead §7.8 directive; combined-reopen checklist; C3 closure template"
    status := VerificationStatus.interface
    note :=
      "NEXT REOPEN SCOPE (deferred to a real closure): registry ONE note only (ids/" ++
        "order/ABC unchanged) -> gate touch+re-pin (41 deps fresh, olean mtime > " ++
        "registry) -> probes recompiled -> acceptance record status/pin updates -> " ++
        "FINAL-ARTIFACTS + ledger + checklist. ONE reopen + ONE re-pin; no gate-v4 " ++
        "promotion; notify all streams."
    dependsOn := [ "S3141SecondReopenChecklistActual" ] }

#check S3142ReopenScopeRecord
#check S3142ReopenScope_length

end LeanFormal.IUT.Audit
