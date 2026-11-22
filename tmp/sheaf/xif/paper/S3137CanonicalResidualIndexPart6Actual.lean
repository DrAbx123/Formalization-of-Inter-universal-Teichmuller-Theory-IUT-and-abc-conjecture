import LeanFormal.IUT.Audit.Status

/-!
# S3137 canonical residual index, part 6 (task-59; stepxi first-triangle integration)

First-triangle integration ids from stepxi's registry data
(`S3139FirstTriangleIntegrationConsumerActual.firstTriangleResidualObligationIds`,
`firstTriangleConstructedIds`).  Aliasing note: stepxi's
`FT.C3.tensor-factor-identification` is the SAME object as the already-indexed
`INDEX.FT.C.ind1-bridge-dependency` (SourceInd1BridgeDependency), so no duplicate
node is created.  Data only; no residual asserted.
-/

namespace LeanFormal.IUT.Audit

/-- first-triangle C2 sub-node: conjugate copy action (aggregate of the local
local element map + capsule fiber assignment).  Exact declarations:
`SourceFmodLocalElementMap` (S3139C2LocalDegreeDataActual) +
`SourceCapsuleFiberAssignment` (S3139C2FiniteCopyActionActual, light version
S3139C2FiniteCopyActionLightActual: sourceFinitePlaceCopyActionData /
SourceCopyActionChannels constructed).  IUT III:616-620, Fig. I.5. -/
def INDEX_FT_C2_conjugateCopyAction : Obligation :=
  { id := "INDEX.FT.C2.conjugate-copy-action"
    source := "IUT III, pp. 616-620, Figure I.5, Remark 3.11.1"
    status := VerificationStatus.pending
    note := "OWNER stepxi. Aggregate of SourceFmodLocalElementMap + SourceCapsuleFiberAssignment; constructed light channels: sourceFinitePlaceCopyActionData / SourceCopyActionChannels (S3139C2FiniteCopyActionLightActual, tensor laws lightInd2_one/lightInd2_mul_apply). NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C", "INDEX.FT.C2.local-element-map", "INDEX.FT.C2.fiber-assignment"] }

/-- first-triangle C2 sub-node: reduction to cross-stream M0/M1.  Exact declaration:
`LGPGlobalUnitsLocalMissing` (stage4 S3136LGPGlobalUnitsToLocalUnitsActual:
sameCIdentification + placeSelection; v2 green). -/
def INDEX_FT_C2_reducesToM0M1 : Obligation :=
  { id := "INDEX.FT.C2.reduces-to-M0-M1"
    source := "IUT III, pp. 616-620, Figure I.5; stepxi S3139C2CoordinationResidualActual"
    status := VerificationStatus.pending
    note := "OWNER stepxi+stage4. Exact declaration: LGPGlobalUnitsLocalMissing (S3136LGPGlobalUnitsToLocalUnitsActual v2, green; sameCIdentification + placeSelection). Cross-stream: depends on M0/R1 same-C id and M1 place selection. NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C", "R1.M0.native-to-OriginalInput", "R1.M1.bad-tensor-index", "LGP.residuals"] }

/-- first-triangle integration node: the conditional theorem.  Exact declaration:
`S3139FirstTriangleIntegrationActual.firstTriangleConditional` (EXIT0 results
143612): from the reduced residual record FirstTriangleRemainingResidual
{infinitePlaceChoice, sourceCapsuleData, sameCIdentification, placeSelection}
and fourth-triangle arithmetic inputs yields copy-action channels + Cor 3.12
ordered conclusion; q-pilot side firstTriangleConditional_qPilot, gluing
firstTriangleConditional_gluing_invariance. -/
def INDEX_FT_conditionalTheorem : Obligation :=
  { id := "INDEX.FT.conditional-theorem"
    source := "IUT III, pp. 616-620, Figure I.5; Corollary 3.12"
    status := VerificationStatus.pending
    note := "OWNER stepxi. Exact declaration: S3139FirstTriangleIntegrationActual.firstTriangleConditional (conditional on FirstTriangleRemainingResidual props, not asserted) + _qPilot + _gluing_invariance. SUPERSEDED/EXTENDED by INDEX.FT.final-composition (S3139FirstTriangleFinalCompositionLightActual.firstTriangleFinalComposition, EXIT0). NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C"] }

/-- first-triangle integration node: public consumer.  Exact declaration:
`S3139FirstTriangleIntegrationConsumerActual.publicFirstTriangleConditional`
(EXIT0 results 144058) plus registry data firstTriangleResidualObligationIds /
firstTriangleConstructedIds. -/
def INDEX_FT_publicConsumer : Obligation :=
  { id := "INDEX.FT.public-consumer"
    source := "IUT III, pp. 616-620, Figure I.5; Corollary 3.12"
    status := VerificationStatus.pending
    note := "OWNER stepxi. Exact declaration: S3139FirstTriangleIntegrationConsumerActual.publicFirstTriangleConditional; registry data firstTriangleResidualObligationIds / firstTriangleConstructedIds. NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C"] }

/-- Part-6 canonical index. -/
def S3137CanonicalResidualIndexPart6 : List Obligation :=
  [ INDEX_FT_C2_conjugateCopyAction,
    INDEX_FT_C2_reducesToM0M1,
    INDEX_FT_conditionalTheorem,
    INDEX_FT_publicConsumer ]

theorem S3137CanonicalResidualIndexPart6_length :
    S3137CanonicalResidualIndexPart6.length = 4 := rfl

end LeanFormal.IUT.Audit