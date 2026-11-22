import LeanFormal.IUT.Audit.Status

/-!
# S3137 canonical residual index, part 8 (stepxi CFT/Kummer integration + tools)

First-triangle C2 Kummer/copy-action ids and two stream tool ids reported by
stepxi (all EXIT0 + trio).  The two tool ids are proved generic tools; they are
listed separately (`S3137StreamToolIndex`) and referenced from the tool
inventory (`S3137ToolInventoryIndexActual`), not counted as residual sub-nodes.
Data only.
-/

namespace LeanFormal.IUT.Audit

/-- first-triangle C2 sub-node (CONSTRUCTED integration node): local Kummer copy
action via existing CFT tools.  Exact declarations:
`S3139C2LocalKummerCopyActual.sourceLocalArtinMap` / `sourceLocalKummerClass` /
`sourceKummerCopyEquiv` (+`_one`/`_mul`); reuses `PadicField.artin`
(Reciprocity/Artin.lean:133) and `KummerTheory.kummer`
(ContinuousKummerTheory/Kummer/Basic.lean:215). -/
def INDEX_FT_C2_kummerCopyAction : Obligation :=
  { id := "INDEX.FT.C2.kummer-copy-action"
    source := "IUT III, pp. 616-620, Figure I.5; local CFT/Artin map; Kummer theory"
    status := VerificationStatus.sourceProjection
    note := "OWNER stepxi. Constructed: S3139C2LocalKummerCopyActual.sourceLocalArtinMap / sourceLocalKummerClass / sourceKummerCopyEquiv (+_one/_mul), reusing PadicField.artin and KummerTheory.kummer (TOOL.EXTERNAL.PADIC.NORM-UNIFORMIZER / TOOL.EXTERNAL.CKT.KUMMER-ROOT). NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C"] }

/-- first-triangle C2 sub-node (EXACT MISSING): Kummer-Artin compatibility.
Exact declaration: `SourceKummerArtinCompatibility` (structure; comparison
ContH1 -> Gal(maxAbelian K, Omega/K) matching both actual maps on copy units).
Refs III:616-620, Fig. I.5. -/
def INDEX_FT_C2_galoisKummerCompat : Obligation :=
  { id := "INDEX.FT.C2.galois-kummer-compat"
    source := "IUT III, pp. 616-620, Figure I.5, Remark 3.11.1"
    status := VerificationStatus.sourceProjection
    note := "OWNER stepxi. SUPERSEDED (no longer missing): the compatibility is now a THEOREM node INDEX.FT.C2.kummer-artin-pairing (S3139C2KummerArtinTheoremActual, constructed from PadicField.pairingH1_kummer). This id is kept only as a data alias; do not count it as a residual. Original exact declaration: SourceKummerArtinCompatibility (S3139C2LocalKummerCopyActual). NOT ABC-strength."
    dependsOn := ["first-triangle.A-C"] }

/-- Stream tool: pi-tensor congruence laws (generic Mathlib-gap tool).  Exact
declarations: `S3139ToolsTensorCongrLaws.piTensorCongr_refl` /
`piTensorCongr_trans_tprod`. -/
def INDEX_TOOL_piTensorCongr : Obligation :=
  { id := "INDEX.TOOL.piTensorCongr"
    source := "generic tensor-product tool (Mathlib gap); IUT III tensor/Hodge structures"
    status := VerificationStatus.provedKernel
    note := "OWNER stepxi (stream tool, manufactured). S3139ToolsTensorCongrLaws.piTensorCongr_refl / piTensorCongr_trans_tprod (EXIT0 + trio). Listed in S3137StreamToolIndex; not a residual. INFO: generic pi-tensor congruence laws reusable by tensor-product consumers."
    dependsOn := [] }

/-- Stream tool: realified-degree to R^x character (generic tool).  Exact
declarations: `S3139ToolsRealUnitCharacter.realUnitCharacterOfMultiplicative`
(+_one/_mul). -/
def INDEX_TOOL_realUnitCharacter : Obligation :=
  { id := "INDEX.TOOL.realUnitCharacter"
    source := "generic realified-degree tool; IUT II/III value-group normalization"
    status := VerificationStatus.provedKernel
    note := "OWNER stepxi (stream tool, manufactured). S3139ToolsRealUnitCharacter.realUnitCharacterOfMultiplicative (+_one/_mul) (EXIT0 + trio). Listed in S3137StreamToolIndex; not a residual. INFO: realified-degree -> R^x character reusable by value-group normalization consumers."
    dependsOn := [] }

/-- Part-8 entries (2 first-triangle C2 sub-nodes + 2 stream tool ids). -/
def S3137CanonicalResidualIndexPart8 : List Obligation :=
  [ INDEX_FT_C2_kummerCopyAction,
    INDEX_FT_C2_galoisKummerCompat,
    INDEX_TOOL_piTensorCongr,
    INDEX_TOOL_realUnitCharacter ]

/-- Stream tool ids (proved tools, not residual sub-nodes). -/
def S3137StreamToolIndex : List (String × String) :=
  [ ("INDEX.TOOL.piTensorCongr", "S3139ToolsTensorCongrLaws.piTensorCongr_refl / piTensorCongr_trans_tprod (stepxi)"),
    ("INDEX.TOOL.realUnitCharacter", "S3139ToolsRealUnitCharacter.realUnitCharacterOfMultiplicative (+_one/_mul) (stepxi)") ]

theorem S3137CanonicalResidualIndexPart8_length :
    S3137CanonicalResidualIndexPart8.length = 4 := rfl

theorem S3137StreamToolIndex_length :
    S3137StreamToolIndex.length = 2 := rfl

end LeanFormal.IUT.Audit