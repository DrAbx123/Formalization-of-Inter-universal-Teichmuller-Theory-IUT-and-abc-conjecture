import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction

/-!
# S1374: corrected signature typing for the D5-D9 source records

Paper anchor: IUT I, Definition 3.1(b) types the F-side `X_F` as a
once-punctured elliptic curve, i.e. of signature `(1,1)`, and Definition
3.1(d) types the K-side `C_K` and `X_K` as `(1,l-tors)^\pm` and
`(1,l-tors)`, with K-core `C_K = C_F x_F K`.  The K-core base change is
coarse: extracting l-th roots of the theta function ([EtTh], Definition 2.1)
adds the l-torsion stacky decoration on the K-side.  It therefore preserves
the genus of the coarse curve, not the full signature (stacky orders and
punctures).

Before the fix, `SourceSignQuotientGeometricCore`,
`SourceCompletionSignQuotient` and `SourceSignQuotientData` forced
`x_F.signature = (1,1)` and `x_K.signature = (1,l-tors)` while
`SourceOrbicurveScalarExtension.signature_preserved` plus
`x_K = xKExtension.result` forced those signatures to be equal.  S1360
turned this into three contradiction theorems.

The fix implemented in `SourceDefinition31Quantifiers` is the
paper-faithful option: keep the paper's F-side `(1,1)` and
K-side `(1,l-tors)` types, and weaken the scalar-extension record to the
one invariant actually preserved by the coarse K-core base change, namely
the genus.  `SourceOrbicurveScalarExtension` now stores
`genus_preserved` only; `signature_preserved`,
`stackyOrders_preserved` and `punctures_preserved` are gone.  Retyping
`X_F` and `C_F` as `(1,l-tors)` was rejected because Definition 3.1(b)
explicitly makes `X_F` once-punctured.

This file records and proves the corrected consequences:

* all three records have the paper signature typing;
* the cross-extension relation is the genus equality;
* the records force `x_K.signature != x_F.signature` (the opposite of the
  old bridge), so no explosion step is used or needed;
* the signature-level constraints are inhabited by the paper's four types;
* the C-side has the paper `(1,l-tors)^\pm` type and genus one.

No geometric record is inhabited here, and no terminal/empty carrier is
used.  This file only verifies that the corrected typing is consistent.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1374SourceSignQuotientFix

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

universe u

/-! ## 1. The paper signatures and their basic relations -/

/-- The paper's F-side `(1,1)` type is the once-punctured elliptic type. -/
theorem s1374_sourceTypeOneOne_eq_oncePunctured :
    sourceTypeOneOne = Iut.OrbicurveSignature.oncePuncturedElliptic := by
  apply Iut.OrbicurveSignature.ext <;> rfl

/-- The F-side `(1,1)` type and the K-side `(1,l-tors)` type differ:
the puncture counts are `1` and `0`. -/
theorem s1374_sourceTypeOneLTorsion_ne_sourceTypeOneOne
    (l : PrimeGeFive) : sourceTypeOneLTorsion l ≠ sourceTypeOneOne := by
  intro h
  have hp : (sourceTypeOneLTorsion l).punctures = sourceTypeOneOne.punctures :=
    congrArg Iut.OrbicurveSignature.punctures h
  simp [sourceTypeOneLTorsion, sourceTypeOneOne] at hp

/-- The K-side `(1,l-tors)` type and the K-side `(1,l-tors)^\pm` type
have the same genus. -/
theorem s1374_sourceTypeOneLTorsion_genus_eq_plusMinus
    (l : PrimeGeFive) :
    (sourceTypeOneLTorsion l).genus =
      (sourceTypeOneLTorsionPlusMinus l).genus :=
  rfl

/-! ## 2. The fixed signature typing of one record -/

/-- Fixed signature typing of one D5-D9 record: the F-side is `(1,1)`, the
K-side is `(1,l-tors)`, the scalar extension gives the common genus, and
the two signatures are distinct.  The distinctness is the corrected
cross-extension relation, not an explosion step. -/
theorem s1374_signature_typing
    {l : PrimeGeFive}
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    {xF : Iut.HyperbolicOrbicurve F} {xK : Iut.HyperbolicOrbicurve K}
    {E : SourceOrbicurveScalarExtension F K xF}
    (hF : xF.signature = sourceTypeOneOne)
    (hK : xK.signature = sourceTypeOneLTorsion l)
    (hEq : xK = E.result) :
    xF.signature = sourceTypeOneOne ∧
    xK.signature = sourceTypeOneLTorsion l ∧
    xK.signature.genus = xF.signature.genus ∧
    xK.signature ≠ xF.signature := by
  refine ⟨hF, hK, ?_, ?_⟩
  · calc
      xK.signature.genus = E.result.signature.genus := by
        rw [hEq]
      _ = xF.signature.genus := E.genus_preserved
  · intro h
    exact s1374_sourceTypeOneLTorsion_ne_sourceTypeOneOne l
      (hK.symm.trans (h.trans hF))

/-- The C-side signature typing: the K-side `(1,l-tors)^\pm` type, the
common genus of `C_F`/`C_K`, and genus one on the F-side.  This uses
only the genus preservation of the fixed scalar extension. -/
theorem s1374_cK_typing
    {l : PrimeGeFive}
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    {cF : Iut.HyperbolicOrbicurve F} {cK : Iut.HyperbolicOrbicurve K}
    {E : SourceOrbicurveScalarExtension F K cF}
    (hK : cK.signature = sourceTypeOneLTorsionPlusMinus l)
    (hEq : cK = E.result) :
    cK.signature = sourceTypeOneLTorsionPlusMinus l ∧
    cK.signature.genus = cF.signature.genus ∧
    cF.signature.genus = 1 := by
  refine ⟨hK, ?_, ?_⟩
  · calc
      cK.signature.genus = E.result.signature.genus := by
        rw [hEq]
      _ = cF.signature.genus := E.genus_preserved
  · calc
      cF.signature.genus = E.result.signature.genus :=
        E.genus_preserved.symm
      _ = cK.signature.genus := by
        rw [hEq]
      _ = 1 := by
        rw [hK]
        rfl

/-- The old full-preservation bridge is not a consequence of the fixed
extension: if the source signature is `(1,1)` and the extension result is
`(1,l-tors)`, then the two signatures cannot be equal.  This is a
negation of the old bridge, not an explosion step. -/
theorem s1374_no_full_signature_preservation
    {l : PrimeGeFive}
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    {xF : Iut.HyperbolicOrbicurve F}
    (E : SourceOrbicurveScalarExtension F K xF)
    (hF : xF.signature = sourceTypeOneOne)
    (hK : E.result.signature = sourceTypeOneLTorsion l) :
    ¬ E.result.signature = xF.signature := by
  intro h
  exact s1374_sourceTypeOneLTorsion_ne_sourceTypeOneOne l
    (hK.symm.trans (h.trans hF))

/-! ## 3. The three records are consistent -/

/-- `SourceSignQuotientGeometricCore`: `X_F` is `(1,1)`, `X_K` is
`(1,l-tors)`, the extension gives the common genus, and the signatures are
distinct. -/
theorem s1374SourceSignQuotientGeometricCore_signature_typing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    G.xF.signature = sourceTypeOneOne ∧
    G.xK.signature = sourceTypeOneLTorsion l ∧
    G.xK.signature.genus = G.xF.signature.genus ∧
    G.xK.signature ≠ G.xF.signature :=
  s1374_signature_typing (l := l)
    G.xF_geometry.signature G.xKType G.xK_eq_extension

/-- `SourceSignQuotientGeometricCore`, C-side: the K-side
`(1,l-tors)^\pm` type, common genus, and genus one on the F-side. -/
theorem s1374SourceSignQuotientGeometricCore_cK_typing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    G.cK.signature = sourceTypeOneLTorsionPlusMinus l ∧
    G.cK.signature.genus = G.cF.signature.genus ∧
    G.cF.signature.genus = 1 :=
  s1374_cK_typing (l := l) G.cKType G.cK_eq_extension

/-- `SourceCompletionSignQuotient`: the completed record has the same
consistent signature typing. -/
theorem s1374SourceCompletionSignQuotient_signature_typing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (C : SourceCompletionSignQuotient A) :
    C.xF.signature = sourceTypeOneOne ∧
    C.xK.signature = sourceTypeOneLTorsion l ∧
    C.xK.signature.genus = C.xF.signature.genus ∧
    C.xK.signature ≠ C.xF.signature :=
  s1374_signature_typing (l := l)
    C.xF_geometry.signature C.xKType C.xK_eq_extension

/-- `SourceCompletionSignQuotient`, C-side. -/
theorem s1374SourceCompletionSignQuotient_cK_typing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (C : SourceCompletionSignQuotient A) :
    C.cK.signature = sourceTypeOneLTorsionPlusMinus l ∧
    C.cK.signature.genus = C.cF.signature.genus ∧
    C.cF.signature.genus = 1 :=
  s1374_cK_typing (l := l) C.cKType C.cK_eq_extension

/-- `SourceSignQuotientData`: the assembled D5-D9 record has the same
consistent signature typing. -/
theorem s1374SourceSignQuotientData_signature_typing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (S : SourceSignQuotientData A) :
    S.xF.signature = sourceTypeOneOne ∧
    S.xK.signature = sourceTypeOneLTorsion l ∧
    S.xK.signature.genus = S.xF.signature.genus ∧
    S.xK.signature ≠ S.xF.signature :=
  s1374_signature_typing (l := l)
    S.xF_geometry.signature S.xKType S.xK_eq_extension

/-- `SourceSignQuotientData`, C-side. -/
theorem s1374SourceSignQuotientData_cK_typing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (S : SourceSignQuotientData A) :
    S.cK.signature = sourceTypeOneLTorsionPlusMinus l ∧
    S.cK.signature.genus = S.cF.signature.genus ∧
    S.cF.signature.genus = 1 :=
  s1374_cK_typing (l := l) S.cKType S.cK_eq_extension

/-! ## 4. The signature-level constraints are inhabited -/

/-- Signature-level shadow of the fixed records.  It records exactly the
signature data and cross-relations that the records impose; it is not a
replacement for the geometric objects. -/
structure S1374SignatureTyping (l : PrimeGeFive) where
  xF : Iut.OrbicurveSignature
  xK : Iut.OrbicurveSignature
  cF : Iut.OrbicurveSignature
  cK : Iut.OrbicurveSignature
  xF_type : xF = sourceTypeOneOne
  xK_type : xK = sourceTypeOneLTorsion l
  cK_type : cK = sourceTypeOneLTorsionPlusMinus l
  xK_genus : xK.genus = xF.genus
  cK_genus : cK.genus = cF.genus

/-- The paper's four types satisfy the fixed signature constraints:
`(1,1)`, `(1,l-tors)`, `(1,1)^\pm`, and `(1,l-tors)^\pm`. -/
def s1374PaperSignatureTyping (l : PrimeGeFive) :
    S1374SignatureTyping l where
  xF := sourceTypeOneOne
  xK := sourceTypeOneLTorsion l
  cF := sourceTypeOneOnePlusMinus
  cK := sourceTypeOneLTorsionPlusMinus l
  xF_type := rfl
  xK_type := rfl
  cK_type := rfl
  xK_genus := rfl
  cK_genus := rfl

/-- The signature-level constraints are satisfiable. -/
theorem s1374PaperSignatureTyping_nonempty (l : PrimeGeFive) :
    Nonempty (S1374SignatureTyping l) :=
  ⟨s1374PaperSignatureTyping l⟩

/-- In any signature shadow the two X-side types are distinct. -/
theorem S1374SignatureTyping.xK_ne_xF
    {l : PrimeGeFive} (T : S1374SignatureTyping l) :
    T.xK ≠ T.xF := by
  intro h
  exact s1374_sourceTypeOneLTorsion_ne_sourceTypeOneOne l
    (T.xK_type.symm.trans (h.trans T.xF_type))

/-- The signature shadow of a geometric core. -/
def S1374SignatureTyping.ofGeometricCore
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    S1374SignatureTyping l where
  xF := G.xF.signature
  xK := G.xK.signature
  cF := G.cF.signature
  cK := G.cK.signature
  xF_type := G.xF_geometry.signature
  xK_type := G.xKType
  cK_type := G.cKType
  xK_genus := by
    calc
      G.xK.signature.genus = G.xKExtension.result.signature.genus := by
        rw [G.xK_eq_extension]
      _ = G.xF.signature.genus := G.xKExtension.genus_preserved
  cK_genus := by
    calc
      G.cK.signature.genus = G.cKExtension.result.signature.genus := by
        rw [G.cK_eq_extension]
      _ = G.cF.signature.genus := G.cKExtension.genus_preserved

/-- The signature shadow of a completion-level record. -/
def S1374SignatureTyping.ofSourceCompletion
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (C : SourceCompletionSignQuotient A) :
    S1374SignatureTyping l where
  xF := C.xF.signature
  xK := C.xK.signature
  cF := C.cF.signature
  cK := C.cK.signature
  xF_type := C.xF_geometry.signature
  xK_type := C.xKType
  cK_type := C.cKType
  xK_genus := by
    calc
      C.xK.signature.genus = C.xKExtension.result.signature.genus := by
        rw [C.xK_eq_extension]
      _ = C.xF.signature.genus := C.xKExtension.genus_preserved
  cK_genus := by
    calc
      C.cK.signature.genus = C.cKExtension.result.signature.genus := by
        rw [C.cK_eq_extension]
      _ = C.cF.signature.genus := C.cKExtension.genus_preserved

/-- The signature shadow of the assembled D5-D9 record. -/
def S1374SignatureTyping.ofSourceSignQuotientData
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (S : SourceSignQuotientData A) :
    S1374SignatureTyping l where
  xF := S.xF.signature
  xK := S.xK.signature
  cF := S.cF.signature
  cK := S.cK.signature
  xF_type := S.xF_geometry.signature
  xK_type := S.xKType
  cK_type := S.cKType
  xK_genus := by
    calc
      S.xK.signature.genus = S.xKExtension.result.signature.genus := by
        rw [S.xK_eq_extension]
      _ = S.xF.signature.genus := S.xKExtension.genus_preserved
  cK_genus := by
    calc
      S.cK.signature.genus = S.cKExtension.result.signature.genus := by
        rw [S.cK_eq_extension]
      _ = S.cF.signature.genus := S.cKExtension.genus_preserved

/-! ## 5. Corrected scalar-extension API -/

#check SourceOrbicurveScalarExtension.signature_genus_preserved
#check @SourceOrbicurveScalarExtension.genus_preserved

/-! ## 6. Axiom footprint -/

#print axioms s1374_sourceTypeOneOne_eq_oncePunctured
#print axioms s1374_sourceTypeOneLTorsion_ne_sourceTypeOneOne
#print axioms s1374_sourceTypeOneLTorsion_genus_eq_plusMinus
#print axioms s1374_signature_typing
#print axioms s1374_cK_typing
#print axioms s1374_no_full_signature_preservation
#print axioms s1374SourceSignQuotientGeometricCore_signature_typing
#print axioms s1374SourceSignQuotientGeometricCore_cK_typing
#print axioms s1374SourceCompletionSignQuotient_signature_typing
#print axioms s1374SourceCompletionSignQuotient_cK_typing
#print axioms s1374SourceSignQuotientData_signature_typing
#print axioms s1374SourceSignQuotientData_cK_typing
#print axioms s1374PaperSignatureTyping_nonempty
#print axioms S1374SignatureTyping.ofGeometricCore
#print axioms S1374SignatureTyping.ofSourceCompletion
#print axioms S1374SignatureTyping.ofSourceSignQuotientData

end LeanFormal.IUT.XiFPaper.S1374SourceSignQuotientFix

end
