import LeanFormal.IUT.Audit.Status

/-!
# S3137 canonical residual index, part 14 (hull Theta-half final composition)

Data only.  Hull's final Theta-half composition nodes (all green + probe trio).
-/

namespace LeanFormal.IUT.Audit

/-- Theta-half final-composition node (THEOREM).  Exact declarations:
`S3132ThetaHalfFinalCompositionActual.thetaHalfFinal_of_uniformComparison_and_normalization`
(MissingC3PacketUniformComparison + MissingThetaLogNormalization =>
MissingFourthTriangleThetaHalfReadout) and
`thetaHalfFinal_of_index_and_fiber_and_normalization` (index + MissingOneColumnC3FiberComparison
+ normalization => target); concrete forms in S3132ThetaHalfConcreteFinalActual:
`thetaHalfFinalConcrete_of_modelTie`, `thetaHalfFinalConcrete_of_modelTie_index_fiber`
(explicit residuals: MissingConcreteC3PlaceTie + index + fiber data + normalization). -/
def INDEX_ThetaHalf_finalComposition : Obligation :=
  { id := "INDEX.ThetaHalf.final-composition"
    source := "IUT III, Proposition 3.9, (i), p. 115; Corollary 3.12, Step (xi-e); Remark 3.9.5"
    status := VerificationStatus.provedKernel
    note := "OWNER hull. FINAL COMPOSITION (conditional): S3132ThetaHalfFinalCompositionActual EXIT0 149977 (thetaHalfFinal_of_uniformComparison_and_normalization; thetaHalfFinal_of_index_and_fiber_and_normalization) + S3132ThetaHalfConcreteFinalActual EXIT0 150019 (thetaHalfFinalConcrete_of_modelTie; thetaHalfFinalConcrete_of_modelTie_index_fiber); probe trio 150058-150069. Depends on ThetaHalf.vform-canonical-residual + ThetaHalf.exact-factor-residual + fiber/C3-place-tie ids (INDEX.R1.C3-place-tie etc.). NOT ABC-strength. PARENT: ThetaHalf.vform-canonical-residual."
    dependsOn := ["ThetaHalf.vform-canonical-residual", "ThetaHalf.exact-factor-residual", "INDEX.R1.C3-place-tie"] }

def S3137CanonicalResidualIndexPart14 : List Obligation :=
  [ INDEX_ThetaHalf_finalComposition ]

theorem S3137CanonicalResidualIndexPart14_length :
    S3137CanonicalResidualIndexPart14.length = 1 := rfl

end LeanFormal.IUT.Audit
