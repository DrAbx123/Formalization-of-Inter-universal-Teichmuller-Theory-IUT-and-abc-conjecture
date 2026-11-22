import LeanFormal.IUT.Audit.Status

/-! # AG95: stepxi AG09 gate ids + canonical Cech paths (lattice binding)

stepxi AG09IdsActual.agGateIds (EXIT0 169889; checker CITABLE): INDEX.AG.cech ->
AG05CechActual; .line-bundle -> AG06LineBundleActual; .RR-Serde-interface ->
AG06bRRInterfaceActual; .mathlib-coverage -> AG07MathlibCoverageActual;
.proof-status -> AG08ProofStatusTableActual (refreshed; recompile pending);
INDEX.GEOMCORE.statement -> GeomCore01StatementActual (statement-only, assembly
gated).  Canonical Cech import paths: AG_FLT_CechPromotionActual (primary) /
AG_FLT_CechSectionsActual / AG_FLT_TwoChartCechActual.  Deprecated not counted:
stepxiAGRRFinishActual, AG05CechPortedActual.  Pins 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.AG95StepXIAG09BindActual

/-- AG09 gate ids bindings (data). -/
def S3137AG09GateIds : List (String × String) :=
  [ ("INDEX.AG.cech", "AG05CechActual (CITABLE 4871B 11 decls 4B32DE2F); canonical imports AG_FLT_CechPromotionActual (primary) / AG_FLT_CechSectionsActual / AG_FLT_TwoChartCechActual"),
    ("INDEX.AG.line-bundle", "AG06LineBundleActual (CITABLE 3269B 9 decls 4E0B7A46)"),
    ("INDEX.AG.RR-Serde-interface", "AG06bRRInterfaceActual"),
    ("INDEX.AG.mathlib-coverage", "AG07MathlibCoverageActual"),
    ("INDEX.AG.proof-status", "AG08ProofStatusTableActual (refreshed; recompile pending)"),
    ("INDEX.GEOMCORE.statement", "GeomCore01StatementActual (statement-only; assembly gated)"),
    ("deprecated-not-counted", "stepxiAGRRFinishActual; AG05CechPortedActual"),
    ("pins", "registry frozen 14041; no registry edits") ]

theorem S3137AG09GateIds_length : S3137AG09GateIds.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.AG95StepXIAG09BindActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: AG09 gate ids + canonical Cech paths. -/
def S3137AG09GateIdsRecord : Obligation :=
  { id := "INDEX.AG.ag09-gate-ids"
    source := "stepxi AG09IdsActual.agGateIds (EXIT0 169889, checker CITABLE); canonical Cech paths AG_FLT_CechPromotionActual/AG_FLT_CechSectionsActual/AG_FLT_TwoChartCechActual"
    status := VerificationStatus.interface
    note := "AG09 GATE IDS bound: INDEX.AG.cech -> AG05CechActual (CITABLE 4B32DE2F; canonical Cech imports AG_FLT_CechPromotionActual primary), .line-bundle -> AG06LineBundleActual (4E0B7A46), .RR-Serde-interface -> AG06bRRInterfaceActual, .mathlib-coverage -> AG07MathlibCoverageActual, .proof-status -> AG08ProofStatusTableActual (refreshed; recompile pending), INDEX.GEOMCORE.statement -> GeomCore01StatementActual (statement-only, assembly gated). Deprecated not counted: stepxiAGRRFinishActual, AG05CechPortedActual. Pins 14041; no registry edits."
    dependsOn := ["AG95StepXIAG09BindActual", "INDEX.AG.cech"] }

end LeanFormal.IUT.Audit
