import LeanFormal.IUT.Audit.Status

/-! # S3141: acceptance-artifact index data (machine-readable subset)

Data rows of the acceptance pair hashes, mirroring
`coord/FINAL-ARTIFACTS-20261110.md`.  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (artifact, src_size, src_sha256 prefix) rows for the acceptance pair. -/
def S3141AcceptancePairRows : List (String × Nat × String) := [
  ("S3140ClosureGateActual.lean", 22958, "41C7ED9606DE20D80C6FFFA356B186EF70725FA6352A72C7957F02F0A778EE3D"),
  ("_S3140ClosureGateAxiomsProbe.lean", 1648, "825FAEC00B23CBFD9C6A7BB20CCA984D3647758296126813566DE7921CB8F0A9"),
  ("_S3140FinalAxiomRecountProbeActual.lean", 21352, "B57E3D7190E1964EC5BA5E0229B03D473E4E09C1543493D216FC2499F85582AC"),
  ("S3140FinalAcceptanceRecordActual.lean", 14932, "13C344D174B990B6D2332707415508345D873B5CE16A9EFF4C23019A89034BBA"),
  ("S3131FinalResidualRegistryActual.lean", 13108, "55012B55582EA268781F5679D496108E9781121331F9E47CB616B2D23FD55801"),
  ("S3139C3ConventionClosureActual.lean", 5576, "69D16A4138477179ED9792F77E9B553CEEC9C2200D871045781854CFB76DEF0D") ]

theorem S3141AcceptancePairRows_length :
    S3141AcceptancePairRows.length = 6 := rfl

/-- Acceptance-index data record. -/
def S3141FinalArtifactsIndexData : Obligation :=
  { id := "IUT.project.final-artifacts-index-data"
    source := "coord/FINAL-ARTIFACTS-20261110.md (post-C3-closure pin)"
    status := VerificationStatus.interface
    note :=
      "MACHINE-READABLE SUBSET of the acceptance pair: gate 22958 (41C7ED96...), gate " ++
        "probe 1648 (825FAEC0...), recount probe 21352 (B57E3D71...), acceptance record " ++
        "14932 (13C344D1...), frozen registry 13108 (55012B55...), C3 closure 5576 " ++
        "(69D16A41...). Full index with olean hashes is coord/FINAL-ARTIFACTS-20261110.md."
    dependsOn :=
      [ "S3140ClosureGateActual", "S3131FinalResidualRegistryActual",
        "S3140FinalAcceptanceRecordActual", "S3139C3ConventionClosureActual" ] }

#check S3141FinalArtifactsIndexData
#check S3141AcceptancePairRows_length

end LeanFormal.IUT.Audit
