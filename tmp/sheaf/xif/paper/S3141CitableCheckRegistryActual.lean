import LeanFormal.IUT.Audit.Status

/-! # S3141: xif_citable_check verdict registry (observed evidence)

Data rows of checker verdicts observed for key artifacts (JSON verdict + counts).
Citable checks are part of the acceptance evidence.  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (artifact, verdict, detail) rows. -/
def S3141CitableCheckVerdicts : List (String × String × String) := [
  ("S3140ClosureGateActual.lean", "CITABLE", "olean fresh; EXIT=0; 2 decls; probe_ok true (post-C3 re-pin)"),
  ("S3140FinalAcceptanceRecordActual.lean", "CITABLE", "olean fresh; EXIT=0; 1 decl; C3 CLOSED folded"),
  ("S3139C3ConventionClosureActual.lean", "CITABLE", "3 decls; probe_ok true; C3 convention closed"),
  ("S3137FromScratchModelSupplyActual.lean", "CITABLE", "7 decls; probe green; task-72 supply (NOT an M1 closure)"),
  ("S3137M1ConcreteDonorActual.lean", "NOT_YET", "probe EXIT=1 pending owner fix"),
  ("S3133M2aClosedActual.lean", "NOT_CITABLE", "doc-only history / EXIT=1 real attempt pending"),
  ("S3135FinalAssemblyGateV4CandidateActual.lean", "NOT_PROMOTED", "green but v4 promotion not approved") ]

theorem S3141CitableCheckVerdicts_length :
    S3141CitableCheckVerdicts.length = 7 := rfl

/-- Citable-check verdict registry. -/
def S3141CitableCheckRegistry : Obligation :=
  { id := "IUT.project.citable-check-registry"
    source :=
      "tools/xif_citable_check.ps1 runs on 2026-11-10; acceptance record; ledger"
    status := VerificationStatus.interface
    note :=
      "OBSERVED CHECKER VERDICTS: gate CITABLE (2 decls, probe_ok), acceptance record " ++
        "CITABLE, C3 closure CITABLE (3 decls, probe_ok), task-72 supply CITABLE (7 " ++
        "decls, probe green; NOT an M1 closure), M1 donor probe NOT_YET (EXIT=1), " ++
        "M2a NOT_CITABLE (doc-only false green history / real attempt EXIT=1), V4 " ++
        "green but NOT_PROMOTED. Verdicts must be re-run after any source/olean change."
    dependsOn := [ "S3140FinalAcceptanceRecordActual" ] }

#check S3141CitableCheckRegistry
#check S3141CitableCheckVerdicts_length

end LeanFormal.IUT.Audit
