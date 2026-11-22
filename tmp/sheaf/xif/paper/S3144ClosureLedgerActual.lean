import LeanFormal.IUT.Audit.Status

/-! # S3144: real-closure ledger data (two closures folded)

Data rows of the two real residual closures and their registry revisions.  No
sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (closure, evidence artifact, registry revision) rows. -/
def S3144ClosureLedger : List (String × String × String) := [
  ("FT.C3.convention-identification", "S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds", "13108 (first reopen)"),
  ("R1.M2a", "S3133M2aClosedActual + S3133M2aNormReductionActual", "13129 (second reopen)"),
  ("R1 residual after closures", "R1 = M1 + M2b; R1.M1 OPEN", "registry 13129 note") ]

theorem S3144ClosureLedger_length : S3144ClosureLedger.length = 3 := rfl

/-- Closure ledger record. -/
def S3144ClosureLedgerRecord : Obligation :=
  { id := "IUT.project.real-closure-ledger"
    source := "registry 13129; acceptance record 15501; ledger entries 04:11 and 04:25"
    status := VerificationStatus.interface
    note :=
      "TWO REAL CLOSURES FOLDED: C3 convention (registry 13108) and M2a (registry " ++
        "13129). Current R1 residual composition: R1 = M1 + M2b (M1 OPEN; M2b exact spec " ++
        "S3133M2bTateQIdentification). No other closure claimed; doc-only artifacts never " ++
        "counted."
    dependsOn :=
      [ "S3139C3ConventionClosureActual", "S3133M2aClosedActual",
        "S3131FinalResidualRegistryActual" ] }

#check S3144ClosureLedgerRecord
#check S3144ClosureLedger_length

end LeanFormal.IUT.Audit
