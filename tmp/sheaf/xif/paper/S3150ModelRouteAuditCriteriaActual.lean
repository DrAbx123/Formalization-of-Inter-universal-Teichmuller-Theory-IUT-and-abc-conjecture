import LeanFormal.IUT.Audit.Status

/-! # S3150: model-route closure audit criteria (how to verify each item)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Per-criterion verification method (data rows). -/
def S3150ModelRouteAuditMethods : List (String × String) := [
  ("(a) package definitionality", "grep the assembled model for package fields with ':= rfl'/definitional proofs; reject any ':= hypothesized' / cross-monoid equality assumption; check binder lists have no extra hypotheses"),
  ("(b) M1 wiring", "xif_citable_check on S3137ModelPlaceToModWiringActual; read modelPlaceToModDataS3135 (ofDistinct/five/inf/rfl) + faithful injectivity; confirm consumed in model assembly"),
  ("(c) M2b descent", "check qVFamily := model q is a definition (rfl-level) and the q-parameter identification theorem is proved for the model, not assumed"),
  ("(d) F4.a/F4.b", "audit the two named lemmas: s3135_valueMonoid_realified_identification (elementary identification) and s3135_procession_scaling_unit_degree_zero (unit-log-zero, non-definitional derivation); trio probes"),
  ("(e) in-model R1", "find the composition theorem assembling R1 = M1 + M2b in the model; verify M0/M3 proved citations; no residual disjunction assumed"),
  ("(f) citable checks", "tools/xif_citable_check.ps1 on every evidence file (+probe); all CITABLE; kernel trio/no-sorry") ]

theorem S3150ModelRouteAuditMethods_length : S3150ModelRouteAuditMethods.length = 6 := rfl

/-- Model-route audit criteria record. -/
def S3150ModelRouteAuditCriteria : Obligation :=
  { id := "IUT.project.model-route-closure-audit-criteria"
    source := "Lead third-reopen directive; audit practice from C3/M2a closures"
    status := VerificationStatus.interface
    note :=
      "AUDIT METHOD: verify each of (a)-(f) by the recorded method; any missing item = NO reopen "
      ++ "request. Do not infer definitionality from compilation; inspect the actual binder "
      ++ "lists/proof terms. Cross-monoid equalities or assumed residual disjunctions are "
      ++ "disqualifying (circularity/triviality)."
    dependsOn := [ "S3150ThirdReopenChecklist" ] }

#check S3150ModelRouteAuditCriteria
#check S3150ModelRouteAuditMethods_length

end LeanFormal.IUT.Audit
