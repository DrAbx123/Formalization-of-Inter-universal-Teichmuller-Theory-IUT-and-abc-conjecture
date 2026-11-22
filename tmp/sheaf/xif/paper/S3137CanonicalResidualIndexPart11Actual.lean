import LeanFormal.IUT.Audit.Status

/-!
# S3137 canonical residual index, part 11 (stepxi C3 convention identification RESOLVED)

C3 convention identification is now a THEOREM (certified CITABLE), and the
generic manufactured tool is registered.  Data only.
-/

namespace LeanFormal.IUT.Audit

/-- first-triangle C3 sub-node: convention identification — RESOLVED THEOREM.
Exact declarations: `S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds`
(+ sourceInd1ConventionComparison / _tprod, conventionFiber / conventionFiberEquiv);
EXIT=0 results 151396; checker CITABLE (3 decls, trio-only); probe
_S3139ConventionClosureProbe results 151497.  Non-circular: the tool is generic
over family/permutation; identification appears only as goal type. -/
def INDEX_FT_C3_convention : Obligation :=
  { id := "INDEX.FT.C3.convention-identification"
    source := "IUT III, pp. 604-620, Figures I.4-I.6; Ind1AutomorphismTensorActionActual.lean:44; S3139C3ConventionClosureActual"
    status := VerificationStatus.provedKernel
    note := "OWNER stepxi. RESOLVED THEOREM (was exact missing): S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds + sourceInd1ConventionComparison/_tprod + conventionFiber/conventionFiberEquiv (EXIT0 results 151396; checker CITABLE, 3 decls, trio-only; probe _S3139ConventionClosureProbe 151497). Uses generic tool INDEX.TOOL.piTensorEntryPermute. Non-circular (PrcAutomorphismTensorAction = production reindex def; polyIsoOfPerm = literal PolyIsoAction; identification only as goal type). NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C", "INDEX.TOOL.piTensorEntryPermute"] }

/-- Stream tool: piTensorEntryPermute (generic manufactured).  Exact declarations:
`S3139ToolsPiTensorEntryPermute.piTensorEntryPermute` / `_tprod`; EXIT0 150781;
checker CITABLE. -/
def INDEX_TOOL_piTensorEntryPermute : Obligation :=
  { id := "INDEX.TOOL.piTensorEntryPermute"
    source := "stepxi manufactured generic tool (pi-tensor entry permute); IUT III convention comparison"
    status := VerificationStatus.provedKernel
    note := "OWNER stepxi. Generic manufactured tool: S3139ToolsPiTensorEntryPermute.piTensorEntryPermute / piTensorEntryPermute_tprod (EXIT0 results 150781; checker CITABLE). Used by INDEX.FT.C3.convention-identification. Not a residual."
    dependsOn := [] }

def S3137CanonicalResidualIndexPart11 : List Obligation :=
  [ INDEX_FT_C3_convention, INDEX_TOOL_piTensorEntryPermute ]

theorem S3137CanonicalResidualIndexPart11_length :
    S3137CanonicalResidualIndexPart11.length = 2 := rfl

end LeanFormal.IUT.Audit
