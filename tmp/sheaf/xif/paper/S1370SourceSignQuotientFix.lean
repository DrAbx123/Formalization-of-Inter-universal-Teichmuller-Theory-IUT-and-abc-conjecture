import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import LeanFormal.IUT.IUTI.InitialTheta.SourceSignQuotientConstruction

/-!
# S1370: consistent signature typing for the D5-D9 sign-quotient records

Paper anchor: IUT I, Definition 3.1(b) (corpus lines 3131-3157) types the
F-side curve X_F as a once-punctured elliptic curve, i.e. of type (1,1),
and Definition 3.1(d) (corpus lines 3185-3215) types the K-side C_K and X_K
as (1,l-tors)^+- and (1,l-tors), with K-core C_K = C_F x_F K.  The K-core
is the coarse base change; extracting l-th roots of the theta function
([EtTh], Definition 2.1) adds the l-torsion stacky decoration on the K-side.

S1360 proved that the previous typing was inconsistent: xF_geometry forced
x_F.signature = sourceTypeOneOne, xKType forced
x_K.signature = sourceTypeOneLTorsion l, and xK_eq_extension together with
the old full signature_preserved forced those two signatures to be equal.

Fix (minimal, paper-faithful): keep the F-side (1,1) and the K-side
(1,l-tors) types, and weaken the K-core scalar extension to the one
invariant preserved by the coarse base change, namely the genus.
`SourceOrbicurveScalarExtension` no longer stores stacky-order or puncture
preservation and no longer proves full signature equality.  Retyping X_F
and C_F as (1,l-tors) was rejected because Definition 3.1(b) explicitly
makes X_F a once-punctured (1,1) curve.

Consequences proved here:

* the three records have exactly the paper signature typing;
* the cross-extension relation is the genus equality;
* the records force x_K.signature != x_F.signature, so the old bridge and
  the three S1360 `False` theorems are gone;
* the signature-level constraints are inhabited by the paper's four types;
* no record is identified with a terminal/empty/fake object.

This file does not construct an inhabitant of any geometric record.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1370SourceSignQuotientFix

universe u

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

/-! ## 1. The two paper signatures are distinct -/

/-- The paper's F-side `(1,1)` type is the once-punctured elliptic type. -/
theorem s1370_sourceTypeOneOne_eq_oncePunctured :
    sourceTypeOneOne = Iut.OrbicurveSignature.oncePuncturedElliptic := by
  apply Iut.OrbicurveSignature.ext <;> rfl

/-- The F-side `(1,1)` type and the K-side `(1,l-tors)` type differ: the
puncture counts are `1` and `0`. -/
theorem s1370_sourceTypeOneLTorsion_ne_sourceTypeOneOne
    (l : PrimeGeFive) : sourceTypeOneLTorsion l ≠ sourceTypeOneOne := by
  intro h
  have hp : (sourceTypeOneLTorsion l).punctures = sourceTypeOneOne.punctures :=
    congrArg Iut.OrbicurveSignature.punctures h
  simp [sourceTypeOneLTorsion, sourceTypeOneOne] at hp

/-! ## 2. The fixed signature typing of one record -/

/-- The fixed signature typing of a D5-D9 record.  The K-core scalar
extension preserves only the genus; the F-side and K-side orbifold types
are the paper's distinct `(1,1)` and `(1,l-tors)`. -/
theorem s1370_signature_typing
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
      xK.signature.genus = E.result.signature.genus :=
        congrArg (fun X => X.signature.genus) hEq
      _ = xF.signature.genus := E.genus_preserved
  · intro h
    have hF' : xF.signature =
        Iut.OrbicurveSignature.oncePuncturedElliptic :=
      hF.trans s1370_sourceTypeOneOne_eq_oncePunctured
    have hlt : sourceTypeOneLTorsion l = sourceTypeOneOne :=
      (hK.symm.trans (h.trans hF')).trans
        s1370_sourceTypeOneOne_eq_oncePunctured.symm
    exact s1370_sourceTypeOneLTorsion_ne_sourceTypeOneOne l hlt

/-- The C-side signature typing of a D5-D9 record: the K-side
`(1,l-tors)^+-` type, the common genus of C_F/C_K, and genus one on the
F-side. -/
theorem s1370_cK_typing
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
      cK.signature.genus = E.result.signature.genus :=
        congrArg (fun X => X.signature.genus) hEq
      _ = cF.signature.genus := E.genus_preserved
  · calc
      cF.signature.genus = E.result.signature.genus :=
        E.genus_preserved.symm
      _ = cK.signature.genus :=
        (congrArg (fun X => X.signature.genus) hEq).symm
      _ = 1 := by
        simp [hK, sourceTypeOneLTorsionPlusMinus]

/-! ## 3. The three records are consistent -/

/-- `SourceSignQuotientGeometricCore`: X_F is (1,1), X_K is (1,l-tors),
the extension gives the common genus, and the signatures are distinct. -/
theorem s1370SourceSignQuotientGeometricCore_signature_typing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    G.xF.signature = sourceTypeOneOne ∧
    G.xK.signature = sourceTypeOneLTorsion l ∧
    G.xK.signature.genus = G.xF.signature.genus ∧
    G.xK.signature ≠ G.xF.signature :=
  s1370_signature_typing (l := l)
    G.xF_geometry.signature G.xKType G.xK_eq_extension

/-- `SourceSignQuotientGeometricCore`: the C-side is consistent too. -/
theorem s1370SourceSignQuotientGeometricCore_cK_typing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    G.cK.signature = sourceTypeOneLTorsionPlusMinus l ∧
    G.cK.signature.genus = G.cF.signature.genus ∧
    G.cF.signature.genus = 1 :=
  s1370_cK_typing (l := l) G.cKType G.cK_eq_extension

/-- `SourceCompletionSignQuotient`: the completed record has the same
consistent signature typing. -/
theorem s1370SourceCompletionSignQuotient_signature_typing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (C : SourceCompletionSignQuotient A) :
    C.xF.signature = sourceTypeOneOne ∧
    C.xK.signature = sourceTypeOneLTorsion l ∧
    C.xK.signature.genus = C.xF.signature.genus ∧
    C.xK.signature ≠ C.xF.signature :=
  s1370_signature_typing (l := l)
    C.xF_geometry.signature C.xKType C.xK_eq_extension

/-- `SourceCompletionSignQuotient`: the C-side is consistent too. -/
theorem s1370SourceCompletionSignQuotient_cK_typing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (C : SourceCompletionSignQuotient A) :
    C.cK.signature = sourceTypeOneLTorsionPlusMinus l ∧
    C.cK.signature.genus = C.cF.signature.genus ∧
    C.cF.signature.genus = 1 :=
  s1370_cK_typing (l := l) C.cKType C.cK_eq_extension

/-- `SourceSignQuotientData`: the assembled D5-D9 record has the same
consistent signature typing. -/
theorem s1370SourceSignQuotientData_signature_typing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (S : SourceSignQuotientData A) :
    S.xF.signature = sourceTypeOneOne ∧
    S.xK.signature = sourceTypeOneLTorsion l ∧
    S.xK.signature.genus = S.xF.signature.genus ∧
    S.xK.signature ≠ S.xF.signature :=
  s1370_signature_typing (l := l)
    S.xF_geometry.signature S.xKType S.xK_eq_extension

/-- `SourceSignQuotientData`: the C-side is consistent too. -/
theorem s1370SourceSignQuotientData_cK_typing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (S : SourceSignQuotientData A) :
    S.cK.signature = sourceTypeOneLTorsionPlusMinus l ∧
    S.cK.signature.genus = S.cF.signature.genus ∧
    S.cF.signature.genus = 1 :=
  s1370_cK_typing (l := l) S.cKType S.cK_eq_extension

/-! ## 4. The signature-level constraints are inhabited -/

/-- Signature-level shadow of the fixed records.  It records exactly the
signature data and cross-relations that the records impose; it is not a
replacement for the geometric objects. -/
structure S1370SignatureTyping (l : PrimeGeFive) where
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
(1,1), (1,l-tors), (1,1)^+-, and (1,l-tors)^+-. -/
def s1370PaperSignatureTyping (l : PrimeGeFive) :
    S1370SignatureTyping l where
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
theorem s1370PaperSignatureTyping_nonempty (l : PrimeGeFive) :
    Nonempty (S1370SignatureTyping l) :=
  ⟨s1370PaperSignatureTyping l⟩

/-- In any signature shadow the two X-side types are distinct. -/
theorem S1370SignatureTyping.xK_ne_xF
    {l : PrimeGeFive} (T : S1370SignatureTyping l) :
    T.xK ≠ T.xF := by
  intro h
  exact s1370_sourceTypeOneLTorsion_ne_sourceTypeOneOne l
    (T.xK_type.symm.trans (h.trans T.xF_type))

/-- The signature shadow of a geometric core. -/
def S1370SignatureTyping.ofGeometricCore
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    S1370SignatureTyping l where
  xF := G.xF.signature
  xK := G.xK.signature
  cF := G.cF.signature
  cK := G.cK.signature
  xF_type := G.xF_geometry.signature
  xK_type := G.xKType
  cK_type := G.cKType
  xK_genus := by
    calc
      G.xK.signature.genus = G.xKExtension.result.signature.genus :=
        congrArg (fun X => X.signature.genus) G.xK_eq_extension
      _ = G.xF.signature.genus := G.xKExtension.genus_preserved
  cK_genus := by
    calc
      G.cK.signature.genus = G.cKExtension.result.signature.genus :=
        congrArg (fun X => X.signature.genus) G.cK_eq_extension
      _ = G.cF.signature.genus := G.cKExtension.genus_preserved

/-- The signature shadow of a completion-level record. -/
def S1370SignatureTyping.ofSourceCompletion
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (C : SourceCompletionSignQuotient A) :
    S1370SignatureTyping l where
  xF := C.xF.signature
  xK := C.xK.signature
  cF := C.cF.signature
  cK := C.cK.signature
  xF_type := C.xF_geometry.signature
  xK_type := C.xKType
  cK_type := C.cKType
  xK_genus := by
    calc
      C.xK.signature.genus = C.xKExtension.result.signature.genus :=
        congrArg (fun X => X.signature.genus) C.xK_eq_extension
      _ = C.xF.signature.genus := C.xKExtension.genus_preserved
  cK_genus := by
    calc
      C.cK.signature.genus = C.cKExtension.result.signature.genus :=
        congrArg (fun X => X.signature.genus) C.cK_eq_extension
      _ = C.cF.signature.genus := C.cKExtension.genus_preserved

/-- The signature shadow of the assembled D5-D9 record. -/
def S1370SignatureTyping.ofSourceSignQuotientData
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (S : SourceSignQuotientData A) :
    S1370SignatureTyping l where
  xF := S.xF.signature
  xK := S.xK.signature
  cF := S.cF.signature
  cK := S.cK.signature
  xF_type := S.xF_geometry.signature
  xK_type := S.xKType
  cK_type := S.cKType
  xK_genus := by
    calc
      S.xK.signature.genus = S.xKExtension.result.signature.genus :=
        congrArg (fun X => X.signature.genus) S.xK_eq_extension
      _ = S.xF.signature.genus := S.xKExtension.genus_preserved
  cK_genus := by
    calc
      S.cK.signature.genus = S.cKExtension.result.signature.genus :=
        congrArg (fun X => X.signature.genus) S.cK_eq_extension
      _ = S.cF.signature.genus := S.cKExtension.genus_preserved

/-! ## 5. Axiom footprint -/

#print axioms s1370_sourceTypeOneOne_eq_oncePunctured
#print axioms s1370_sourceTypeOneLTorsion_ne_sourceTypeOneOne
#print axioms s1370_signature_typing
#print axioms s1370_cK_typing
#print axioms s1370SourceSignQuotientGeometricCore_signature_typing
#print axioms s1370SourceSignQuotientGeometricCore_cK_typing
#print axioms s1370SourceCompletionSignQuotient_signature_typing
#print axioms s1370SourceCompletionSignQuotient_cK_typing
#print axioms s1370SourceSignQuotientData_signature_typing
#print axioms s1370SourceSignQuotientData_cK_typing
#print axioms s1370PaperSignatureTyping_nonempty
#print axioms S1370SignatureTyping.ofGeometricCore
#print axioms S1370SignatureTyping.ofSourceCompletion
#print axioms S1370SignatureTyping.ofSourceSignQuotientData

end LeanFormal.IUT.XiFPaper.S1370SourceSignQuotientFix

end
