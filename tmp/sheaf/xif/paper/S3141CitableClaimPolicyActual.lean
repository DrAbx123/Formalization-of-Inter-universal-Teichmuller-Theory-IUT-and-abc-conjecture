import LeanFormal.IUT.Audit.Status

/-! # S3141: citable-claim verification policy (mandatory)

Record of the verification rule adopted after two false greens (stale gate 21906,
doc-only M2a 147613).  Citable/closed claims require EXIT=0 + fresh olean + ACTUAL
declarations + trio/no-axiom probe, checked statically by
`tools/xif_citable_check.ps1`.  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- The four mandatory conditions for a citable/closed claim. -/
def S3141CitableConditions : List String := [
  "last results.log line for the file is EXIT=0",
  "olean is fresh (olean mtime >= source mtime)",
  "file contains ACTUAL declarations (theorem/def/instance: not comment- or doc-only)",
  "probe is green with trio/no-axiom footprints and no sorryAx" ]

theorem S3141CitableConditions_length :
    S3141CitableConditions.length = 4 := rfl

/-- Known false-green incidents that motivated the rule. -/
def S3141FalseGreenIncidents : List String := [
  "stale gate 21906 (dep olean changed; watchdog does not recompile consumers)",
  "doc-only M2a 147613 / S3133M2aClosedActual (0 declarations, not a closure)" ]

theorem S3141FalseGreenIncidents_length :
    S3141FalseGreenIncidents.length = 2 := rfl

/-- Citable-claim policy record. -/
def S3141CitableClaimPolicy : Obligation :=
  { id := "IUT.project.citable-claim-policy"
    source :=
      "Lead verification rule (post false-green incidents); tools/xif_citable_check.ps1; " ++
        "S3140FinalAcceptanceRecordActual; AUDIT_LEDGER"
    status := VerificationStatus.interface
    note :=
      "MANDATORY: a citable/closed claim needs EXIT=0 + fresh olean + ACTUAL " ++
        "declarations (comment/doc-only is NOT evidence) + green trio/no-axiom probe " ++
        "without sorryAx; verify with tools/xif_citable_check.ps1 -File <f> [-Probe <p>]. " ++
        "Log parsing alone is NOT evidence (false greens: stale gate 21906; doc-only M2a " ++
        "147613). Closure claims additionally need semantic check that the residual " ++
        "actually closes (not renamed/weakened/trivial/concrete-only for a general claim)."
    dependsOn := [ "S3140FinalAcceptanceRecordActual" ] }

#check S3141CitableClaimPolicy
#check S3141CitableConditions_length
#check S3141FalseGreenIncidents_length

end LeanFormal.IUT.Audit
