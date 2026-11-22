import LeanFormal.IUT.Audit.Status

/-!
# S3137 canonical residual index, part 13 (stepxi final first-triangle composition)

Record-only update (registry frozen): the conditional first-triangle theorem is
superseded/extended by the final composition theorem.  Data only.
-/

namespace LeanFormal.IUT.Audit

/-- first-triangle final composition node (THEOREM).  Exact declarations:
`S3139FirstTriangleFinalCompositionLightActual.firstTriangleFinalComposition`
(final conditional theorem) + `FirstTriangleFinalResidual` + 
`sourceArchimedeanCopyActionDataOfActual` (archimedean channel from the resolved
C1).  Supersedes/extends INDEX.FT.conditional-theorem. -/
def INDEX_FT_finalComposition : Obligation :=
  { id := "INDEX.FT.final-composition"
    source := "IUT III, pp. 616-620, Figure I.5; Corollary 3.12; first-triangle final composition"
    status := VerificationStatus.provedKernel
    note := "OWNER stepxi. FINAL COMPOSITION theorem: S3139FirstTriangleFinalCompositionLightActual.firstTriangleFinalComposition + FirstTriangleFinalResidual + sourceArchimedeanCopyActionDataOfActual (EXIT0 results 149921; probe _S3139FinalCompositionProbe 150009 trio; residual structure no axioms). Supersedes/extends INDEX.FT.conditional-theorem. NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C"] }

def S3137CanonicalResidualIndexPart13 : List Obligation :=
  [ INDEX_FT_finalComposition ]

theorem S3137CanonicalResidualIndexPart13_length :
    S3137CanonicalResidualIndexPart13.length = 1 := rfl

end LeanFormal.IUT.Audit
