import LeanFormal.IUT.Audit.Status

/-!
# S3137 canonical residual index, part 4 (task-59; stepxi first-triangle C/C2)

New first-triangle C/C2 sub-nodes reported by stepxi, under parent
`first-triangle.A-C`.  Unique `INDEX.` ids; data only; no residual asserted.
Several C2 components are CONSTRUCTED (archimedean realification, copy-action
channels, completion unit maps, local-degree channel); only the exact missing
structures are indexed as residual nodes.  Refs: IUT III:616-620, Fig. I.5,
Remark 3.11.1 unless noted.
-/

namespace LeanFormal.IUT.Audit

/-- first-triangle C1 sub-node: infinite-place choice.  Exact declaration:
`SourceInfinitePlaceChoice` (def Type, S3139FieldCArchimedeanLogActual; no
infinite-place field in InitialThetaArithmeticData, so this is a genuine choice
datum).  Constructed from it: sourceFmodArchimedeanScalarCharacter,
sourceInfinitePlaceScalarCharacter, sourceFmodArchimedeanLog. -/
def INDEX_FT_C1_infinitePlaceChoice : Obligation :=
  { id := "INDEX.FT.C1.infinite-place-choice"
    source := "IUT III, pp. 616-620, Figure I.5, Remark 3.11.1"
    status := VerificationStatus.provedKernel
    note := "OWNER stepxi. RESOLVED as theorem (task-67 update): S3139C1InfinitePlaceActual.sourceInfinitePlaceChoice_nonempty / sourceInfinitePlaceChoiceActual / sourceArchimedeanScalarActual / sourceArchimedeanRealification_nonempty (EXIT0; probe trio) — number-field infinite places exist (Mathlib) and classical choice supplies the place. Original declaration SourceInfinitePlaceChoice (S3139FieldCArchimedeanLogActual). NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C"] }

/-- first-triangle C2 sub-node: local element map.  Exact declaration:
`SourceFmodLocalElementMap` (structure, S3139C2LocalDegreeDataActual); the
local degree channel is constructed given it.  IUT III:616-620, Fig. I.5. -/
def INDEX_FT_C2_localElementMap : Obligation :=
  { id := "INDEX.FT.C2.local-element-map"
    source := "IUT III, pp. 616-620, Figure I.5, Remark 3.11.1"
    status := VerificationStatus.pending
    note := "OWNER stepxi. Exact declaration: SourceFmodLocalElementMap (structure; S3139C2LocalDegreeDataActual); localDegree/localDegreeAdd/localScalarUnit channel constructed given it. NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C"] }

/-- first-triangle C2 sub-node: capsule fiber assignment.  Exact declaration:
`SourceCapsuleFiberAssignment` (structure, S3139C2FiniteCopyActionActual);
depends on the place-index comparison (qpilot M1).  IUT III:616-620, Fig. I.5. -/
def INDEX_FT_C2_fiberAssignment : Obligation :=
  { id := "INDEX.FT.C2.fiber-assignment"
    source := "IUT III, pp. 616-620, Figure I.5, Remark 3.11.1"
    status := VerificationStatus.pending
    note := "OWNER stepxi (with qpilot M1 place-index). Exact declaration: SourceCapsuleFiberAssignment (structure; S3139C2FiniteCopyActionActual); finite copy action constructed given it. NOT ABC-strength. PARENT: first-triangle.A-C; dependsOn also qpilot M1 INDEX/registry (place-index injection)."
    dependsOn := ["first-triangle.A-C", "R1.M1.bad-tensor-index"] }

/-- first-triangle C sub-node: Ind1 bridge dependency.  Exact declaration:
`SourceInd1BridgeDependency` (Prop, S3139FieldCConjugateActual; minimal
dependency on (A) SourceCapsuleSourceDataMissing). -/
def INDEX_FT_C_ind1Bridge : Obligation :=
  { id := "INDEX.FT.C.ind1-bridge-dependency"
    source := "IUT III, pp. 616-620, Figure I.5; Ind1 condition"
    status := VerificationStatus.provedKernel
    note := "OWNER stepxi. DISCHARGED (task-67 update): S3139C3Ind1BridgeActual.sourceInd1BridgeDependency_Real_holds (EXIT0) via sourceCapsuleSourceDataStandard. ALIAS: stepxi registry id FT.C3.tensor-factor-identification is the same object (no duplicate node). Remaining C3 residual is INDEX.FT.C3.convention-identification (SourceInd1ConventionIdentification). NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C"] }

/-- first-triangle C2 coordination node (no separate missing structure): after
coordination C2 is NOT independent missing data; it reduces to (a) same-C
identification F ~ Fmod (M0/R1, lattice/mainline), (b) place selection
V -> C3.tensorIndex (qpilot M1), plus stage4 canonical unit map
(lgpGlobalUnitsToLocalUnits) and local degree readout. -/
def INDEX_FT_C2_coordination : Obligation :=
  { id := "INDEX.FT.C2.coordination"
    source := "IUT III, pp. 616-620, Figure I.5; S3139C2CoordinationResidualActual doc; shehdd SourceDefinition31DualContractAlignment.lean:88"
    status := VerificationStatus.pending
    note := "OWNER stepxi+shehdd+mainline+qpilot. NO separate missing structure: C2 reduces to same-C M0/R1 identification, M1 place selection, stage4 lgpGlobalUnitsToLocalUnits, and local degree readout. NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C", "R1.M0.native-to-OriginalInput", "R1.M1.bad-tensor-index", "LGP.residuals"] }

/-- Part-4 canonical index. -/
def S3137CanonicalResidualIndexPart4 : List Obligation :=
  [ INDEX_FT_C1_infinitePlaceChoice,
    INDEX_FT_C2_localElementMap,
    INDEX_FT_C2_fiberAssignment,
    INDEX_FT_C_ind1Bridge,
    INDEX_FT_C2_coordination ]

theorem S3137CanonicalResidualIndexPart4_length :
    S3137CanonicalResidualIndexPart4.length = 5 := rfl

end LeanFormal.IUT.Audit