import LeanFormal.IUT.Audit.Status

/-! # S3217: 2.4 (M2) P1 application + (M1a) growth + Hull12 Ob9 bound transfer audit

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Rows. -/
def S3217Audit : List (String × String × Nat × Nat × String) := [
  ("Mzk1Lemma24P1ApplicationActual.lean", "CITABLE", 3, 3830, "69B36A105177237E"),
  ("Mzk1Lemma24GrowthActual.lean", "CITABLE", 1, 4592, "A71E29D7394E4B92"),
  ("Hull12Ob9BoundTransferActual.lean", "CITABLE", 4, 4453, "555164AEA2BE0077") ]

theorem S3217Audit_length : S3217Audit.length = 3 := rfl

/-- Content. -/
def S3217Content : List String := [
  "(M2) s3135_p1Morphism_preserves_of_belyi PROVED: constructs actual nonconstant P1Morphism Qbar via Belyification (mapPoints x |-> aeval x q) and proves PreservesSet of finite set into {0,1,infty} — (M2) P1 interface/application layer PROVED (not just statement)",
  "(M1a) s3135_monic_growth_of_coeff_bound PROVED: monic p degree d with coeff bound C => |p.eval z| >= b for |z| >= b + C*d (explicit real-argument proof) => M1a GROWTH PROVED",
  "Hull12Ob9BoundTransfer: 4 decls bound-transfer layer for H7/Ob9 (probe _Hull12ProbeActual green)",
  "remaining: AvoidsPoint beta (Lemma2.3 normalization wiring after growth) + UnramifiedOver unramifiedAt data interface -> Mzk1Lemma24StatementShape; H6 partial" ]

theorem S3217Content_length : S3217Content.length = 4 := rfl

/-- Record. -/
def S3217AuditRecord : Obligation :=
  { id := "IUT.project.m2-m1a-hull12-audit"
    source := "Lead/mainline audit requests 2026-11-10 19:09; checker+probes"
    status := VerificationStatus.interface
    note :=
      "2.4 (M2) + (M1a) + HULL12: Mzk1Lemma24P1Application CITABLE 3 decls 3830B "
      ++ "(s3135_p1Morphism_preserves_of_belyi PROVED: real nonconstant P1Morphism via "
      ++ "Belyification with PreservesSet; remaining AvoidsPoint/UnramifiedOver clauses named). "
      ++ "Mzk1Lemma24Growth CITABLE 1 decl 4592B (s3135_monic_growth_of_coeff_bound PROVED => "
      ++ "M1a GROWTH PROVED). Hull12Ob9BoundTransfer CITABLE 4 decls 4453B (probe green). "
      ++ "Remaining: AvoidsPoint beta wiring + UnramifiedOver data -> StatementShape; H6."
    dependsOn := [ "S3216UnramifiedGateAuditRecord" ] }

#check S3217AuditRecord
#check S3217Audit_length
#check S3217Content_length

end LeanFormal.IUT.Audit
