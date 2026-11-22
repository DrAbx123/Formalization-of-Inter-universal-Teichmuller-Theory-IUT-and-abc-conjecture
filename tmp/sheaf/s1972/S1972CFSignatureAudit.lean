import tmp.sheaf.xif.paper.S1964QuotientCFActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

/-!
# S1972: audit of the C_F / C_K signature labels

This file records, as Lean statements, the numerical part of the S1972 audit.
It does not change any production definition and it does not postulate a
quotient orbicurve.

Sources:

* IUT I (May 2020), Definition 3.1(b): C_F is the hyperbolic orbicurve
  obtained as the stack-theoretic quotient of the once-punctured elliptic
  curve X_F by -1; (b) also assumes the 2*3-torsion of E_F rational over F.
* IUT I, Definition 3.1(d): C_K := C_F x_F K is the K-core, and a finite
  etale covering C_K^-> -> C_K of degree l of type (1,l-tors)^± is
  determined; X_K^-> := C_K^-> x_{C_K} X_K -> X_K is the corresponding
  degree-l cover, of type (1,l-tors).
* [EtTh] (December 2008), Section 0: an orbicurve of type (1,1)^± is the
  quotient of a type-(1,1) stable log curve by the action of ±1.
  Definition 2.1 and 2.3 introduce (1,l-tors)^± and (1,l-tors_Theta)^±
  by the same quotient construction.
* [AbsAnab II] (October 2013), Section 0: a semi-elliptic orbicurve, i.e.
  of type (1,1)^±, is a hyperbolic orbicurve with a finite etale double
  covering by a once-punctured elliptic curve, namely the stack quotient by
  ±1.

Hence the paper's ^± is a construction type, not a numerical signature.
The honest orbifold signature of C_F = [X_F/{±1}] is (0; [2,2,2]; 1), with
orbifold Euler characteristic -1/2; this is the signature realized by the
actual S1726 model in S1964.  The Lean label
sourceTypeOneOnePlusMinus = (1; [2]; 0) is therefore a transcription error,
not a second convention.  Its Euler characteristic happens to be -1/2 as
well, so Euler-characteristic and hyperbolicity checks cannot detect the
error.

The K-side labels in the source contract are also attached to the wrong
objects: SourceSignQuotientData has only the K-cores xK = xF x K and
cK = cF x K, while sourceTypeOneLTorsion and sourceTypeOneLTorsionPlusMinus
are the paper's names for the degree-l covers X_K^-> and C_K^->.  The honest
signatures are

    X_K (core)      : (1; []; 1)                    chi = -1
    C_K (core)      : (0; [2,2,2]; 1)               chi = -1/2
    X_K^->          : (1; []; l)                    chi = -l
    C_K^->          : (0; [2,2,2]; (l+1)/2)         chi = -l/2

For C_K^->, the origin cusp and the three two-torsion points are fixed by the
involution; the other l-1 cusps are paired, giving 1+(l-1)/2 = (l+1)/2
cusps.  None of the Lean labels (1; [l]; 0), (1; [2,l]; 0) matches either the
core or the l-tors object.

The signature component of Iut.HyperbolicOrbicurve is free metadata
(EtaleStackOverField.orbicurveSignature : Option OrbicurveSignature is a
field, and realizedHyperbolicOrbicurve inserts it by construction), so no
Lean contradiction follows from the mislabelling.  The exact missing datum is
the quotient structure S1964FirstMissing together with a formal bridge from
the [EtTh] type names to OrbicurveSignature; neither is in the tree.
-/

noncomputable section

namespace LeanFormal.IUT.InitialThetaSource.S1972CFSignatureAudit

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual

/-! ## 1. The honest C_F signature and the Lean (1,1)^± label -/

/-- The paper-forced signature of C_F = [X_F/{±1}]: genus 0, three
order-two stacky points (the rational two-torsion points), one cusp (the
image of the origin).  Realized for the actual S1726 model by S1964. -/
abbrev paperCF : Iut.OrbicurveSignature := S1964HonestQuotientSignature

/-- The Lean transcription sourceTypeOneOnePlusMinus = (1; [2]; 0) of the
paper type (1,1)^±. -/
abbrev paperLabelCF : Iut.OrbicurveSignature := sourceTypeOneOnePlusMinus

theorem paperCF_genus : paperCF.genus = 0 := rfl

theorem paperCF_stackyOrders : paperCF.stackyOrders = [2, 2, 2] := rfl

theorem paperCF_punctures : paperCF.punctures = 1 := rfl

theorem paperCF_data :
    paperCF.genus = 0 ∧ paperCF.stackyOrders = [2, 2, 2] ∧
      paperCF.punctures = 1 :=
  ⟨paperCF_genus, paperCF_stackyOrders, paperCF_punctures⟩

theorem paperCF_euler : paperCF.eulerCharacteristic = -1 / 2 :=
  S1964HonestQuotientSignature_euler

theorem paperCF_hyperbolic : paperCF.IsHyperbolic :=
  S1964HonestQuotientSignature_hyperbolic

theorem paperLabelCF_genus : paperLabelCF.genus = 1 := rfl

theorem paperLabelCF_stackyOrders : paperLabelCF.stackyOrders = [2] := rfl

theorem paperLabelCF_punctures : paperLabelCF.punctures = 0 := rfl

theorem paperLabelCF_data :
    paperLabelCF.genus = 1 ∧ paperLabelCF.stackyOrders = [2] ∧
      paperLabelCF.punctures = 0 :=
  ⟨paperLabelCF_genus, paperLabelCF_stackyOrders, paperLabelCF_punctures⟩

theorem paperLabelCF_euler : paperLabelCF.eulerCharacteristic = -1 / 2 := by
  norm_num [paperLabelCF, sourceTypeOneOnePlusMinus,
    Iut.OrbicurveSignature.eulerCharacteristic]

theorem paperLabelCF_hyperbolic : paperLabelCF.IsHyperbolic :=
  sourceTypeOneOnePlusMinus_hyperbolic

/-- The error is invisible to the Euler characteristic: both labels give
-1/2. -/
theorem paperLabelCF_euler_eq_paperCF :
    paperLabelCF.eulerCharacteristic = paperCF.eulerCharacteristic := by
  rw [paperLabelCF_euler, paperCF_euler]

/-- The label is not the honest signature: genus 1 versus genus 0 (also
[2] versus [2,2,2], and 0 versus 1 punctures). -/
theorem paperLabelCF_ne_paperCF : paperLabelCF ≠ paperCF := by
  intro h
  have hg : paperLabelCF.genus = paperCF.genus :=
    congrArg Iut.OrbicurveSignature.genus h
  rw [paperLabelCF_genus, paperCF_genus] at hg
  exact Nat.one_ne_zero hg

/-- The coarse quotient (0; []; 1) is not the honest signature either: the
three order-two stacky points are essential. -/
theorem coarseCF_ne_paperCF :
    S1964CoarseQuotientSignature ≠ paperCF := by
  intro h
  have hs : S1964CoarseQuotientSignature.stackyOrders =
      paperCF.stackyOrders :=
    congrArg Iut.OrbicurveSignature.stackyOrders h
  rw [show S1964CoarseQuotientSignature.stackyOrders = [] from rfl,
    paperCF_stackyOrders] at hs
  have hlen := congrArg List.length hs
  simp at hlen

/-- The degree-two {±1}-torsor X_F -> C_F: the orbifold Euler
characteristic of C_F is half that of the once-punctured elliptic curve. -/
theorem paperCF_euler_two_mul :
    2 * paperCF.eulerCharacteristic =
      Iut.OrbicurveSignature.oncePuncturedElliptic.eulerCharacteristic := by
  rw [paperCF_euler,
    Iut.OrbicurveSignature.oncePuncturedElliptic_eulerCharacteristic]
  norm_num

/-- Compact summary of the C_F label comparison. -/
theorem s1972_cF_summary :
    paperLabelCF.genus = 1 ∧ paperLabelCF.stackyOrders = [2] ∧
      paperLabelCF.punctures = 0 ∧ paperCF.genus = 0 ∧
      paperCF.stackyOrders = [2, 2, 2] ∧ paperCF.punctures = 1 ∧
      paperLabelCF.eulerCharacteristic = paperCF.eulerCharacteristic ∧
      paperLabelCF ≠ paperCF :=
  ⟨paperLabelCF_genus, paperLabelCF_stackyOrders, paperLabelCF_punctures,
    paperCF_genus, paperCF_stackyOrders, paperCF_punctures,
    paperLabelCF_euler_eq_paperCF, paperLabelCF_ne_paperCF⟩

/-! ## 2. The legacy SourceOrbicurveSignature labels

SourceInitialThetaData has a second signature structure (with the same three
fields) and a second set of labels.  In ClauseD the source contract attaches
typeOneOne = (1; []; 1) to cF, i.e. it gives C_F the signature of X_F.
-/

/-- Compare the legacy SourceOrbicurveSignature labels with the
Iut.OrbicurveSignature of the actual stack. -/
def toIutSignature (s : SourceOrbicurveSignature) : Iut.OrbicurveSignature where
  genus := s.genus
  stackyOrders := s.stackyOrders
  punctures := s.punctures
  stackyOrders_ge_two := s.stackyOrders_ge_two

@[simp] theorem toIutSignature_genus (s : SourceOrbicurveSignature) :
    (toIutSignature s).genus = s.genus := rfl

@[simp] theorem toIutSignature_stackyOrders (s : SourceOrbicurveSignature) :
    (toIutSignature s).stackyOrders = s.stackyOrders := rfl

@[simp] theorem toIutSignature_punctures (s : SourceOrbicurveSignature) :
    (toIutSignature s).punctures = s.punctures := rfl

/-- The source contract's cF_type label (1; []; 1) is the X_F signature, not
the quotient signature. -/
theorem legacyTypeOneOne_ne_paperCF :
    toIutSignature SourceOrbicurveSignature.typeOneOne ≠ paperCF := by
  intro h
  have hg := congrArg Iut.OrbicurveSignature.genus h
  rw [toIutSignature_genus,
    show SourceOrbicurveSignature.typeOneOne.genus = 1 from rfl,
    paperCF_genus] at hg
  exact Nat.one_ne_zero hg

/-- The two Lean C_F labels in the tree, (1,1)^± = (1; [2]; 0) and
typeOneOne = (1; []; 1), are also not the same signature. -/
theorem paperLabelCF_ne_legacyTypeOneOne :
    paperLabelCF ≠ toIutSignature SourceOrbicurveSignature.typeOneOne := by
  intro h
  have hp := congrArg Iut.OrbicurveSignature.punctures h
  rw [paperLabelCF_punctures, toIutSignature_punctures,
    show SourceOrbicurveSignature.typeOneOne.punctures = 1 from rfl] at hp
  exact Nat.zero_ne_one hp

/-! ## 3. The K-side honest signatures

The paper has four K-side objects, but the Lean source contract has only the
two K-cores (scalar extensions of xF and cF).  The labels typeOneLTorsion and
typeOneLTorsionPlusMinus are the paper's names for the degree-l covers, not
for the cores.
-/

/-- Honest signature of the paper's type-(1,l-tors) curve X_K^->: genus 1,
no stacky points, l cusps. -/
def honestXKTors (l : PrimeGeFive) : Iut.OrbicurveSignature where
  genus := 1
  stackyOrders := []
  punctures := l.value
  stackyOrders_ge_two := by simp

/-- Honest signature of the paper's type-(1,l-tors)^± orbicurve C_K^->:
genus 0, three order-two stacky points, (l+1)/2 cusps. -/
def honestCKTors (l : PrimeGeFive) : Iut.OrbicurveSignature where
  genus := 0
  stackyOrders := [2, 2, 2]
  punctures := (l.value + 1) / 2
  stackyOrders_ge_two := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide

theorem honestXKTors_data (l : PrimeGeFive) :
    (honestXKTors l).genus = 1 ∧ (honestXKTors l).stackyOrders = [] ∧
      (honestXKTors l).punctures = l.value :=
  ⟨rfl, rfl, rfl⟩

theorem honestCKTors_data (l : PrimeGeFive) :
    (honestCKTors l).genus = 0 ∧
      (honestCKTors l).stackyOrders = [2, 2, 2] ∧
      (honestCKTors l).punctures = (l.value + 1) / 2 :=
  ⟨rfl, rfl, rfl⟩

theorem honestXKTors_euler (l : PrimeGeFive) :
    (honestXKTors l).eulerCharacteristic = -(l.value : ℚ) := by
  norm_num [honestXKTors, Iut.OrbicurveSignature.eulerCharacteristic]

theorem honestCKTors_euler (l : PrimeGeFive) :
    (honestCKTors l).eulerCharacteristic = -(l.value : ℚ) / 2 := by
  have hodd : Odd l.value := l.odd
  rcases hodd with ⟨m, hm⟩
  have hdiv : (l.value + 1) / 2 = m + 1 := by omega
  simp only [honestCKTors, Iut.OrbicurveSignature.eulerCharacteristic]
  norm_num
  rw [hdiv, hm]
  norm_num
  ring

theorem honestXKTors_hyperbolic (l : PrimeGeFive) :
    (honestXKTors l).IsHyperbolic := by
  rw [Iut.OrbicurveSignature.IsHyperbolic, honestXKTors_euler]
  have h5 : (5 : ℚ) ≤ (l.value : ℚ) := by
    have := l.ge_five
    exact_mod_cast this
  linarith

theorem honestCKTors_hyperbolic (l : PrimeGeFive) :
    (honestCKTors l).IsHyperbolic := by
  rw [Iut.OrbicurveSignature.IsHyperbolic, honestCKTors_euler]
  have h5 : (5 : ℚ) ≤ (l.value : ℚ) := by
    have := l.ge_five
    exact_mod_cast this
  linarith

/-- Degree-l etale X_K^-> -> X_K: the l-tors cover multiplies the orbifold
Euler characteristic by l. -/
theorem honestXKTors_euler_eq_l_mul_oncePunctured (l : PrimeGeFive) :
    (honestXKTors l).eulerCharacteristic =
      (l.value : ℚ) *
        Iut.OrbicurveSignature.oncePuncturedElliptic.eulerCharacteristic := by
  rw [honestXKTors_euler,
    Iut.OrbicurveSignature.oncePuncturedElliptic_eulerCharacteristic]
  ring

/-- Degree-l etale C_K^-> -> C_K: the l-tors cover multiplies the orbifold
Euler characteristic by l. -/
theorem honestCKTors_euler_eq_l_mul_paperCF (l : PrimeGeFive) :
    (honestCKTors l).eulerCharacteristic =
      (l.value : ℚ) * paperCF.eulerCharacteristic := by
  rw [honestCKTors_euler, paperCF_euler]
  ring

/-- Degree-two {±1}-torsor X_K^-> -> C_K^->. -/
theorem honestXKTors_euler_eq_two_mul_honestCKTors (l : PrimeGeFive) :
    (honestXKTors l).eulerCharacteristic =
      2 * (honestCKTors l).eulerCharacteristic := by
  rw [honestXKTors_euler, honestCKTors_euler]
  ring

/-- The Lean (1,l-tors) label (1; [l]; 0) is not the honest signature of the
l-tors curve (1; []; l). -/
theorem legacyTypeOneLTorsion_ne_honestXKTors (l : PrimeGeFive) :
    toIutSignature (SourceOrbicurveSignature.typeOneLTorsion l) ≠
      honestXKTors l := by
  intro h
  have hp := congrArg Iut.OrbicurveSignature.punctures h
  rw [toIutSignature_punctures,
    show (SourceOrbicurveSignature.typeOneLTorsion l).punctures = 0 from rfl,
    show (honestXKTors l).punctures = l.value from rfl] at hp
  have h5 := l.ge_five
  omega

/-- The Lean (1,l-tors)^± label (1; [2,l]; 0) is not the honest signature of
C_K^-> either. -/
theorem legacyTypeOneLTorsionPlusMinus_ne_honestCKTors (l : PrimeGeFive) :
    toIutSignature (SourceOrbicurveSignature.typeOneLTorsionPlusMinus l) ≠
      honestCKTors l := by
  intro h
  have hg := congrArg Iut.OrbicurveSignature.genus h
  rw [toIutSignature_genus,
    show (SourceOrbicurveSignature.typeOneLTorsionPlusMinus l).genus = 1 from rfl,
    show (honestCKTors l).genus = 0 from rfl] at hg
  exact Nat.one_ne_zero hg

/-- In particular the (1,l-tors)^± label is not the K-core signature
(0; [2,2,2]; 1). -/
theorem legacyTypeOneLTorsionPlusMinus_ne_paperCF (l : PrimeGeFive) :
    toIutSignature (SourceOrbicurveSignature.typeOneLTorsionPlusMinus l) ≠
      paperCF := by
  intro h
  have hg := congrArg Iut.OrbicurveSignature.genus h
  rw [toIutSignature_genus,
    show (SourceOrbicurveSignature.typeOneLTorsionPlusMinus l).genus = 1 from rfl,
    paperCF_genus] at hg
  exact Nat.one_ne_zero hg

/-! ## 4. The production sign-quotient contract

SourceSignQuotientData has no signature field for cF; it derives
cF.signature.genus = 1 from the cK label and genus preservation.  That derived
genus is incompatible with the paper-forced genus 0.  It also labels the
K-cores xK, cK with the l-tors types.
-/

theorem sourceSignQuotientData_cF_genus
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) : S.cF.signature.genus = 1 :=
  SourceSignQuotientData.cF_genus S

/-- The production sign-quotient's cF metadata cannot be the honest C_F
signature (genus 1 versus 0). -/
theorem sourceSignQuotientData_cF_ne_paperCF
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) : S.cF.signature ≠ paperCF := by
  intro h
  have hg := congrArg Iut.OrbicurveSignature.genus h
  rw [sourceSignQuotientData_cF_genus S, paperCF_genus] at hg
  exact Nat.one_ne_zero hg

/-- The production sign-quotient's cK label (1; [2,l]; 0) is not the K-core
signature (0; [2,2,2]; 1). -/
theorem sourceSignQuotientData_cK_ne_paperCF
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) : S.cK.signature ≠ paperCF := by
  intro h
  have hg := congrArg Iut.OrbicurveSignature.genus h
  rw [SourceSignQuotientData.cK_signature S,
    show (sourceTypeOneLTorsionPlusMinus l).genus = 1 from rfl,
    paperCF_genus] at hg
  exact Nat.one_ne_zero hg

/-- The production sign-quotient's xK label (1; [l]; 0) is not the signature
(1; []; 1) of the base-changed once-punctured elliptic curve. -/
theorem sourceSignQuotientData_xK_ne_oncePunctured
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.xK.signature ≠ Iut.OrbicurveSignature.oncePuncturedElliptic := by
  intro h
  have hs := congrArg Iut.OrbicurveSignature.stackyOrders h
  rw [SourceSignQuotientData.xK_signature S,
    show (sourceTypeOneLTorsion l).stackyOrders = [l.value] from rfl,
    show Iut.OrbicurveSignature.oncePuncturedElliptic.stackyOrders = [] from rfl]
    at hs
  simp at hs

/-- The xF component, by contrast, is correctly labelled: it is the
once-punctured elliptic curve. -/
theorem sourceSignQuotientData_xF_eq_oncePunctured
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.xF.signature = Iut.OrbicurveSignature.oncePuncturedElliptic :=
  SourceSignQuotientData.xF_once_punctured S

/-! ## 5. Pointer to the exact missing datum

The label question cannot be settled by the quotient fiber alone: the missing
object is S1964's quotient structure.  No quotient stack is constructed or
postulated here.
-/

theorem exactMissing_iff_quotientStructure (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    S1964FirstMissing l A ↔ Nonempty (S1964QuotientStructure l A) :=
  Iff.rfl

/-! ## 6. Axiom footprint -/

#print axioms paperCF_data
#print axioms paperLabelCF_data
#print axioms paperLabelCF_euler
#print axioms paperLabelCF_ne_paperCF
#print axioms paperCF_euler_two_mul
#print axioms s1972_cF_summary
#print axioms legacyTypeOneOne_ne_paperCF
#print axioms honestCKTors_euler
#print axioms honestXKTors_euler
#print axioms sourceSignQuotientData_cF_ne_paperCF
#print axioms sourceSignQuotientData_cK_ne_paperCF
#print axioms sourceSignQuotientData_xK_ne_oncePunctured

end LeanFormal.IUT.InitialThetaSource.S1972CFSignatureAudit
