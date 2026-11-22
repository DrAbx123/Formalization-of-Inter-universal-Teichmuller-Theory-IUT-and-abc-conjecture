import LeanFormal.IUT.Audit.Status

/-! # S3144: M2a closure evidence bundle (second real residual closure)

Machine-readable evidence bundle for the M2a closure folded into registry 13129.
No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (artifact, src_size, sha256 prefix, checker verdict) rows for the M2a closure. -/
def S3144M2aEvidenceBundle : List (String × Nat × String × String) := [
  ("S3133M2aClosedActual.lean", 5173, "30E910B2C6A729721927BD7D38FC0CEB5731DD079B8BBD89ADAF1D6A4C6C9669", "CITABLE, 6 decls, probe_ok"),
  ("S3133M2aNormReductionActual.lean", 3200, "6B08130333CD5D4EF5261F54B2A7F159984CB43816127535B55080013C71FE21", "CITABLE, 2 decls, probe_ok"),
  ("S3131FinalResidualRegistryActual.lean", 13129, "0518E5322D2BCC7D22DA692894B5D844EAA81D5741AB094CA51421A85E567CD3", "frozen registry note: R1 = M1 + M2b"),
  ("S3140FinalAcceptanceRecordActual.lean", 15501, "23525F60735E2B8F0FC7A3373DA0A1F113905D7F92847A73271E59B6F044EF7C", "CITABLE; M2a CLOSED folded") ]

theorem S3144M2aEvidenceBundle_length : S3144M2aEvidenceBundle.length = 4 := rfl

/-- M2a evidence bundle record. -/
def S3144M2aEvidenceBundleRecord : Obligation :=
  { id := "IUT.project.m2a-closure-evidence-bundle"
    source := "S3133M2aClosedActual + S3133M2aNormReductionActual; registry 13129 note; acceptance record 15501"
    status := VerificationStatus.interface
    note :=
      "M2a CLOSED (SECOND real residual closure): S3133M2aClosedActual (6 decls, CITABLE, " ++
        "probe_ok; norm=5^-1 + canonical Gaussian q-norm + isometry transport) + " ++
        "S3133M2aNormReductionActual (2 decls, CITABLE, probe_ok); R1 = M1 + M2b; folded " ++
        "into registry 13129 and the acceptance record (SIZE 15501). Doc-only false green " ++
        "147613 not counted (retained in the verification rule)."
    dependsOn :=
      [ "S3133M2aClosedActual", "S3133M2aNormReductionActual",
        "S3131FinalResidualRegistryActual" ] }

#check S3144M2aEvidenceBundleRecord
#check S3144M2aEvidenceBundle_length

end LeanFormal.IUT.Audit
