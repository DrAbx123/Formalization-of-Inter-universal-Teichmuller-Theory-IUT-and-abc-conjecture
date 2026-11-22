import LeanFormal.IUT.Audit.Status

/-!
# S3137 canonical residual index, part 10 (stepxi Kummer-Artin theorem update)

`INDEX.FT.C2.galois-kummer-compat` changed from data to THEOREM: the
compatibility is now constructed (`SourceKummerArtinPairingCompatibility`),
using the external Brauer tool `PadicField.pairingH1_kummer`.  A negative node
records the refuted hom-level form.  Data only.
-/

namespace LeanFormal.IUT.Audit

/-- first-triangle C2 sub-node (THEOREM, was missing): Kummer-Artin pairing
compatibility.  Exact declarations: `S3139C2KummerArtinTheoremActual.
SourceKummerArtinPairingCompatibility` (Prop), `sourceKummerArtinPairingCompatibility`,
`_nonempty`, `sourceKummerArtinPairing_eq` (EXIT0), constructed from external
Brauer tool `PadicField.pairingH1_kummer` (Brauer/DualityH1.lean:110). -/
def INDEX_FT_C2_kummerArtinPairing : Obligation :=
  { id := "INDEX.FT.C2.kummer-artin-pairing"
    source := "IUT III, pp. 616-620, Figure I.5; local CFT/Kummer pairing; Brauer/DualityH1.lean:110"
    status := VerificationStatus.provedKernel
    note := "OWNER stepxi. THEOREM (was missing): S3139C2KummerArtinTheoremActual.SourceKummerArtinPairingCompatibility (Prop) + sourceKummerArtinPairingCompatibility / _nonempty / sourceKummerArtinPairing_eq (EXIT0 results 148515; probe _S3139KummerArtinProbe trio), constructed from TOOL.EXTERNAL.BRAUER pairing PadicField.pairingH1_kummer. NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C", "INDEX.TOOL.brauer-pairing"] }

/-- first-triangle C2 sub-node (NEGATIVE node): hom-level form refuted.
Exact declaration: `S3139C2KummerArtinTheoremActual.
kummerHomLevel_forces_artin_pow_trivial` — the hom-level form would force
Artin to kill n-th powers; this route is a model error, kept negative. -/
def INDEX_FT_C2_homLevelRefuted : Obligation :=
  { id := "INDEX.FT.C2.hom-level-refuted"
    source := "IUT III, pp. 616-620, Figure I.5 (hom-level variant refuted)"
    status := VerificationStatus.pending
    note := "OWNER stepxi. NEGATIVE node (model error, not promoted): S3139C2KummerArtinTheoremActual.kummerHomLevel_forces_artin_pow_trivial — a hom-level compatibility form would force Artin to kill n-th powers, so that form is refuted; the correct pairing-compatibility theorem node is indexed separately. NOT ABC-strength. PARENT: first-triangle.A-C."
    dependsOn := ["first-triangle.A-C"] }

/-- Stream tool id: external Brauer pairing (no manufacture needed).  Exact
declaration: `PadicField.pairingH1_kummer` (Brauer/DualityH1.lean:110). -/
def INDEX_TOOL_brauerPairing : Obligation :=
  { id := "INDEX.TOOL.brauer-pairing"
    source := "external Brauer library (Brauer/DualityH1.lean:110)"
    status := VerificationStatus.interface
    note := "EXTERNAL TOOL: PadicField.pairingH1_kummer (Brauer library, olean built; module root NOT LeanFormal.IUT.*). Used by INDEX.FT.C2.kummer-artin-pairing. No manufacture needed. Not a residual."
    dependsOn := [] }

def S3137CanonicalResidualIndexPart10 : List Obligation :=
  [ INDEX_FT_C2_kummerArtinPairing, INDEX_FT_C2_homLevelRefuted, INDEX_TOOL_brauerPairing ]

theorem S3137CanonicalResidualIndexPart10_length :
    S3137CanonicalResidualIndexPart10.length = 3 := rfl

end LeanFormal.IUT.Audit
