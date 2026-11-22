import LeanFormal.IUT.Audit.Status

/-! # S3142: C3 closure evidence bundle (kernel-visible data)

Machine-readable bundle of the FIRST REAL RESIDUAL CLOSURE evidence.  No
sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (artifact, src_size, sha256 prefix, checker verdict) rows for the C3 closure. -/
def S3142C3EvidenceBundle : List (String × Nat × String × String) := [
  ("S3139C3ConventionClosureActual.lean", 5576, "69D16A4138477179ED9792F77E9B553CEEC9C2200D871045781854CFB76DEF0D", "CITABLE"),
  ("_S3139C3ConventionClosureAxiomsProbe.lean", 986, "0CC4FB934F99510E21C0ED608F7E52E457A93EC7BAF587B5A875995890F0DF4B", "trio/no-sorry"),
  ("S3139ToolsPiTensorEntryPermute.lean", 2429, "56F814CA2DA289018F3B9F66E451A7649BF6CA91183CA1F93959A24C3678274E", "CITABLE"),
  ("S3139C3Ind1BridgeActual.lean", 0, "definition file: SourceInd1ConventionIdentification", "no statement change"),
  ("S3139C3ConventionTheoremActual.lean", 3523, "in-place relabeling law used by the closure", "trio") ]

theorem S3142C3EvidenceBundle_length : S3142C3EvidenceBundle.length = 5 := rfl

/-- C3 evidence bundle record. -/
def S3142EvidenceBundleC3 : Obligation :=
  { id := "IUT.project.c3-closure-evidence-bundle"
    source := "S3139C3ConventionClosureActual + probe + manufactured tool; registry 13108 note"
    status := VerificationStatus.interface
    note :=
      "C3 CONVENTION CLOSED (first real residual closure): theorem " ++
        "sourceInd1ConventionIdentification_holds (no extra hypotheses), CITABLE, " ++
        "trio/no-sorry, non-circular; manufactured generic tool " ++
        "S3139ToolsPiTensorEntryPermute; folded into registry 13108 note and the " ++
        "acceptance record (SIZE 14932)."
    dependsOn :=
      [ "S3139C3ConventionClosureActual", "S3139ToolsPiTensorEntryPermute",
        "S3131FinalResidualRegistryActual" ] }

#check S3142EvidenceBundleC3
#check S3142C3EvidenceBundle_length

end LeanFormal.IUT.Audit
