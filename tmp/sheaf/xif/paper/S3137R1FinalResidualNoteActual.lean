import LeanFormal.IUT.Audit.Status

/-! # S3137: R1 final residual interface pointing (qpilot S3133GaussianModelMapResidualFinalActual)

qpilot's R1 final residual file is CHECKER CITABLE (EXIT0 5382, declarations 6,
probe _S3133Batch21 EXIT0 trio).  It exposes R1 = M1 + M2b formally:
* structure S3133GaussianModelMapResidualFinal (D) with only m1_indexInjection and
  m2b_clauseB;
* S3133GaussianModelMapRemainingFinal;
* m0/m3 proved (not residual);
* def of_minimal;
* S3133GaussianQParameterMatchAtBase_iff_clauseB;
* S3137R1_interface_final.
This note points the INDEX R1 entries at those declarations (registry frozen;
mainline applies the narrow note edit).
-/

namespace LeanFormal.IUT.Audit

/-- R1 final-residual interface record (declaration pointers). -/
def S3137R1FinalResidualRecord : Obligation :=
  { id := "INDEX.R1.final-residual-interface"
    source := "qpilot S3133GaussianModelMapResidualFinalActual (EXIT0 5382, 6 decls, probe _S3133Batch21 trio); IUT III Definition 3.8, Corollary 3.12"
    status := VerificationStatus.interface
    note := "R1 = M1 + M2b FORMALLY EXPOSED: S3133GaussianModelMapResidualFinal (D) with only m1_indexInjection + m2b_clauseB; S3133GaussianModelMapRemainingFinal; m0/m3 proved; of_minimal; S3133GaussianQParameterMatchAtBase_iff_clauseB; S3137R1_interface_final. qpilot file checker CITABLE. M2a and C3 are CLOSED; remaining R1 residual = M1 (bad<->C3 tensor index + placeToMod provenance) + M2b (Tate-q clause-B). Registry frozen; one narrow mainline note edit only."
    dependsOn := ["S3133GaussianModelMapResidualFinalActual", "INDEX.R1.M2b.tate-q-identification", "INDEX.MODEL.from-scratch-place-to-mod"] }

end LeanFormal.IUT.Audit
