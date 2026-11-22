import tmp.sheaf.xif.paper.S1983EtThSignatureBridgeActual

/-!
# S1991: corrected (paper-faithful) target aliases for C_F

S1983 bridged the [EtTh] type name (1,1)^± to the honest orbifold signature

    S1991HonestCFSignature = etthSignature EtThType.oneOnePlusMinus
                            = (0; [2,2,2]; 1)

and proved that this is not the legacy Lean label
sourceTypeOneOnePlusMinus = (1; [2]; 0).

The production structures S1932CFQuotient, S1886PaperCF and
S1964CFQuotientAt carry the legacy label.  For the M4 target-lock decision
this file takes the paper-faithful, additive option:

* production definitions are not changed;
* corrected target aliases are placed next to the legacy ones, using the
  honest signature and the [EtTh] type name (1,1)^±;
* the honest and legacy versions are proved to have the same inhabitedness
  (they describe the same quotient structure, with only the stored signature
  changed);
* the exact first missing datum is identified.

The relabelling bridge changes the stored signature on the same etale-stack
fiber (HyperbolicOrbicurve stores it in EtaleStackOverField.orbicurveSignature);
the quotient morphism and the bicategorical universal property only see
stack.fiber, so they are preserved.  This is the same pattern as
S1886CFMetadataRelabel and realizedHyperbolicOrbicurve, applied here to a
quotient structure.

Consequently the label is target data, not a geometric consequence of the
fiber (S1983 G2: S1983SignatureNotForcedByFiber).  The corrected target makes
the paper signature assumed data.  If one demands that the signature be
computed from the quotient geometry, the production signature field must be
changed; that is out of scope and is not claimed.

The exact first missing for the corrected targets is G1:

    S1964FirstMissing l A = Nonempty (S1964QuotientStructure l A),

i.e. the quotient stack [X_F/{±1}], its functoriality/stackification and its
bicategorical universal property.  G2 remains a precise target-adequacy gap:
the type does not force the label to be computed from the fiber, as recorded
by S1991HonestSignatureNotForcedByFiber.

No production definition is modified.  No axiom, sorry, admit or arbitrary
carrier is introduced.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1991HonestTargetAliasesActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.S1972CFSignatureAudit
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual
open LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual
open LeanFormal.IUT.XiFPaper.S1886D9OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1983EtThSignatureBridgeActual

universe u

/-! ## 1. The corrected signature and the [EtTh] type name -/

/-- The [EtTh] type name of C_F: (1,1)^±. -/
abbrev S1991PaperCFType : EtThType := EtThType.oneOnePlusMinus

/-- The corrected paper-faithful signature of C_F: the honest [EtTh] (1,1)^±
signature (0; [2,2,2]; 1), not the legacy label (1; [2]; 0). -/
abbrev S1991HonestCFSignature : Iut.OrbicurveSignature :=
  etthSignature S1991PaperCFType

/-- The corrected signature is the [EtTh] (1,1)^± signature. -/
theorem S1991HonestCFSignature_eq_etth :
    S1991HonestCFSignature = etthSignature S1991PaperCFType := rfl

/-- The corrected signature is S1964's honest quotient signature. -/
theorem S1991HonestCFSignature_eq_S1964HonestQuotientSignature :
    S1991HonestCFSignature = S1964HonestQuotientSignature :=
  etthSignature_oneOnePlusMinus_eq_honestSignature

/-- The corrected signature is S1972's paperCF. -/
theorem S1991HonestCFSignature_eq_paperCF :
    S1991HonestCFSignature = paperCF :=
  etthSignature_oneOnePlusMinus_eq_paperCF

/-- The literal form of the corrected signature: (0; [2,2,2]; 1). -/
def S1991HonestCFSignatureLiteral : Iut.OrbicurveSignature where
  genus := 0
  stackyOrders := [2, 2, 2]
  punctures := 1
  stackyOrders_ge_two := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide

/-- The corrected signature is literally (0; [2,2,2]; 1). -/
theorem S1991HonestCFSignature_eq_literal :
    S1991HonestCFSignature = S1991HonestCFSignatureLiteral := by
  apply Iut.OrbicurveSignature.ext <;> rfl

@[simp] theorem S1991HonestCFSignature_genus :
    S1991HonestCFSignature.genus = 0 := rfl

@[simp] theorem S1991HonestCFSignature_stackyOrders :
    S1991HonestCFSignature.stackyOrders = [2, 2, 2] := rfl

@[simp] theorem S1991HonestCFSignature_punctures :
    S1991HonestCFSignature.punctures = 1 :=
  etthSignature_oneOnePlusMinus_punctures

/-- The numerical data of the corrected target. -/
theorem S1991HonestCFSignature_data :
    S1991HonestCFSignature.genus = 0 ∧
      S1991HonestCFSignature.stackyOrders = [2, 2, 2] ∧
        S1991HonestCFSignature.punctures = 1 :=
  ⟨S1991HonestCFSignature_genus, S1991HonestCFSignature_stackyOrders,
    S1991HonestCFSignature_punctures⟩

/-- The corrected signature has orbifold Euler characteristic -1/2. -/
theorem S1991HonestCFSignature_euler :
    S1991HonestCFSignature.eulerCharacteristic = -1 / 2 :=
  etthSignature_oneOnePlusMinus_euler

/-- Euler-characteristic tests cannot distinguish the honest signature from
the legacy label: both have Euler characteristic -1/2. -/
theorem S1991HonestCFSignature_euler_eq_legacy :
    S1991HonestCFSignature.eulerCharacteristic =
      sourceTypeOneOnePlusMinus.eulerCharacteristic :=
  etthSignature_oneOnePlusMinus_euler_eq_paperLabel

/-- The corrected signature is hyperbolic. -/
theorem S1991HonestCFSignature_hyperbolic :
    S1991HonestCFSignature.IsHyperbolic :=
  etthSignature_oneOnePlusMinus_hyperbolic

/-- The corrected signature is not the legacy label (1; [2]; 0). -/
theorem S1991HonestCFSignature_ne_legacy :
    S1991HonestCFSignature ≠ sourceTypeOneOnePlusMinus :=
  etthSignature_oneOnePlusMinus_ne_sourceTypeOneOnePlusMinus

/-- The data of the legacy label: (1; [2]; 0). -/
theorem S1991LegacyCFSignature_data :
    sourceTypeOneOnePlusMinus.genus = 1 ∧
      sourceTypeOneOnePlusMinus.stackyOrders = [2] ∧
        sourceTypeOneOnePlusMinus.punctures = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- The corrected and legacy labels differ in all three invariants: the
correction is not a cosmetic relabelling of the same numerical signature. -/
theorem S1991HonestCFSignature_vs_legacy :
    S1991HonestCFSignature.genus = 0 ∧
      sourceTypeOneOnePlusMinus.genus = 1 ∧
      S1991HonestCFSignature.stackyOrders = [2, 2, 2] ∧
        sourceTypeOneOnePlusMinus.stackyOrders = [2] ∧
          S1991HonestCFSignature.punctures = 1 ∧
            sourceTypeOneOnePlusMinus.punctures = 0 :=
  ⟨S1991HonestCFSignature_genus, S1991LegacyCFSignature_data.1,
    S1991HonestCFSignature_stackyOrders, S1991LegacyCFSignature_data.2.1,
    S1991HonestCFSignature_punctures, S1991LegacyCFSignature_data.2.2⟩

/-! ## 2. Relabelling along the underlying fiber -/

/-- Change the stored signature of a hyperbolic orbicurve on the same
etale-stack fiber.  The geometric content (the fiber and its stack condition)
is unchanged; only the orbicurveSignature metadata is replaced. -/
noncomputable abbrev S1991Relabel {F : Type u} [Field F]
    (X : Iut.HyperbolicOrbicurve F) (s : Iut.OrbicurveSignature)
    (hs : s.IsHyperbolic) : Iut.HyperbolicOrbicurve F :=
  realizedHyperbolicOrbicurve F X.stack.fiber X.stack.isStack s hs

@[simp] theorem S1991Relabel_signature {F : Type u} [Field F]
    (X : Iut.HyperbolicOrbicurve F) (s : Iut.OrbicurveSignature)
    (hs : s.IsHyperbolic) :
    (S1991Relabel X s hs).signature = s := rfl

@[simp] theorem S1991Relabel_stack_fiber {F : Type u} [Field F]
    (X : Iut.HyperbolicOrbicurve F) (s : Iut.OrbicurveSignature)
    (hs : s.IsHyperbolic) :
    (S1991Relabel X s hs).stack.fiber = X.stack.fiber := rfl

/-- Transport a sign-invariant quotient morphism to a relabelled target.
The underlying morphism is unchanged because Hom only depends on the
underlying etale-stack fibers. -/
noncomputable def S1991InvariantMorphismRelabel {F : Type u} [Field F]
    {X Y : Iut.HyperbolicOrbicurve F}
    {A : Iut.OrbicurveSignAction X}
    (s : Iut.OrbicurveSignature) (hs : s.IsHyperbolic)
    (q : Iut.OrbicurveSignInvariantMorphism A Y) :
    Iut.OrbicurveSignInvariantMorphism A (S1991Relabel Y s hs) where
  map := q.map
  invariant := q.invariant
  cocycle := q.cocycle

/-- Transport the universal property to a relabelled quotient.  The witness
only depends on the underlying fibers, so the same descend, factor and
two-cell data apply. -/
noncomputable def S1991QuotientWitnessRelabel {F : Type u} [Field F]
    {X C : Iut.HyperbolicOrbicurve F}
    {A : Iut.OrbicurveSignAction X}
    {q : Iut.OrbicurveSignInvariantMorphism A C}
    (s : Iut.OrbicurveSignature) (hs : s.IsHyperbolic)
    (w : Iut.OrbicurveSignQuotientWitness A q) :
    Iut.OrbicurveSignQuotientWitness A
      (S1991InvariantMorphismRelabel s hs q) where
  descend := w.descend
  factor := w.factor
  descendTwoCell := w.descendTwoCell
  descendTwoCell_factor := w.descendTwoCell_factor
  twoCell_ext := w.twoCell_ext

/-! ## 3. The S1964 parameterized target: honest next to legacy -/

/-- The S1964 target at the corrected honest label (0; [2,2,2]; 1). -/
abbrev S1991HonestCFQuotientAt (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) :=
  S1964CFQuotientAt l A S1991HonestCFSignature
    S1991HonestCFSignature_hyperbolic

/-- The S1964 target at the legacy label (1; [2]; 0), named explicitly so the
two versions can be placed side by side. -/
abbrev S1991LegacyCFQuotientAt (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) :=
  S1964CFQuotientAt l A sourceTypeOneOnePlusMinus
    sourceTypeOneOnePlusMinus_hyperbolic

/-- The honest S1964 target is exactly S1983's [EtTh]-typed target. -/
theorem S1991HonestCFQuotientAt_eq_S1983EtThCF (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    S1991HonestCFQuotientAt l A = S1983EtThCF l A := rfl

/-- The honest S1964 target is exactly S1964's honest-labelled target. -/
theorem S1991HonestCFQuotientAt_eq_S1964HonestCFQuotient (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    S1991HonestCFQuotientAt l A = S1964HonestCFQuotient l A := rfl

/-- Change the signature label of a parameterized quotient target.  The
quotient morphism and the universal property are preserved on the same
fiber. -/
noncomputable def S1991CFQuotientAtChangeLabel {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    {s t : Iut.OrbicurveSignature} {hs : s.IsHyperbolic}
    (ht : t.IsHyperbolic) (Q : S1964CFQuotientAt l A s hs) :
    S1964CFQuotientAt l A t ht where
  cF := S1991Relabel Q.cF t ht
  cF_signature := rfl
  quotient := S1991InvariantMorphismRelabel t ht Q.quotient
  quotientWitness := S1991QuotientWitnessRelabel t ht Q.quotientWitness

/-- Any two hyperbolic labels give the same inhabitedness for the
parameterized quotient target. -/
theorem S1991CFQuotientAt_nonempty_iff_of_label {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    {s t : Iut.OrbicurveSignature} (hs : s.IsHyperbolic)
    (ht : t.IsHyperbolic) :
    Nonempty (S1964CFQuotientAt l A s hs) ↔
      Nonempty (S1964CFQuotientAt l A t ht) := by
  constructor
  · rintro ⟨Q⟩
    exact ⟨S1991CFQuotientAtChangeLabel ht Q⟩
  · rintro ⟨Q⟩
    exact ⟨S1991CFQuotientAtChangeLabel hs Q⟩

/-- The honest and legacy parameterized targets have the same inhabitedness. -/
theorem S1991HonestCFQuotientAt_nonempty_iff_legacy
    (l : PrimeGeFive) (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    Nonempty (S1991HonestCFQuotientAt l A) ↔
      Nonempty (S1991LegacyCFQuotientAt l A) :=
  S1991CFQuotientAt_nonempty_iff_of_label
    S1991HonestCFSignature_hyperbolic sourceTypeOneOnePlusMinus_hyperbolic

/-- Construct the honest parameterized target from a label-free quotient
structure.  This is the load-bearing step for the equivalence below. -/
noncomputable def S1991CFQuotientAtOfStructure {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (Q : S1964QuotientStructure l A) : S1991HonestCFQuotientAt l A where
  cF := S1991Relabel Q.cF S1991HonestCFSignature
    S1991HonestCFSignature_hyperbolic
  cF_signature := rfl
  quotient := S1991InvariantMorphismRelabel S1991HonestCFSignature
    S1991HonestCFSignature_hyperbolic Q.quotient
  quotientWitness := S1991QuotientWitnessRelabel S1991HonestCFSignature
    S1991HonestCFSignature_hyperbolic Q.quotientWitness

/-- The honest parameterized target is nonempty exactly when the label-free
quotient structure exists. -/
theorem S1991HonestCFQuotientAt_nonempty_iff_firstMissing
    (l : PrimeGeFive) (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    Nonempty (S1991HonestCFQuotientAt l A) ↔ S1964FirstMissing l A := by
  constructor
  · rintro ⟨Q⟩
    exact S1964FirstMissing_ofAt ⟨Q⟩
  · rintro ⟨Q⟩
    exact ⟨S1991CFQuotientAtOfStructure Q⟩

/-! ## 4. The S1932 target: honest next to legacy -/

/-- The corrected S1932 target: identical to S1932CFQuotient except that the
quotient carries the honest signature (0; [2,2,2]; 1) instead of the legacy
label (1; [2]; 0). -/
structure S1991HonestCFQuotient (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) where
  /-- The quotient orbicurve C_F. -/
  cF : Iut.HyperbolicOrbicurve (S1732A l).F
  /-- The corrected paper signature of C_F. -/
  cF_signature : cF.signature = S1991HonestCFSignature
  /-- The sign-invariant quotient morphism X_F -> C_F. -/
  quotient : Iut.OrbicurveSignInvariantMorphism A cF
  /-- The universal property of the quotient. -/
  quotientWitness : Iut.OrbicurveSignQuotientWitness A quotient

/-- The legacy S1932 target, named explicitly for the side-by-side
comparison. -/
abbrev S1991LegacyCFQuotient (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) :=
  S1932CFQuotient l A

/-- Forget the honest label of the S1932 target into the parameterized S1964
target. -/
def S1991HonestCFQuotient.toAt {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (Q : S1991HonestCFQuotient l A) :
    S1991HonestCFQuotientAt l A :=
  ⟨Q.cF, Q.cF_signature, Q.quotient, Q.quotientWitness⟩

/-- Regard the parameterized honest target as the S1932-shaped target. -/
def S1991HonestCFQuotient.ofAt {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (Q : S1991HonestCFQuotientAt l A) :
    S1991HonestCFQuotient l A :=
  ⟨Q.cF, Q.cF_signature, Q.quotient, Q.quotientWitness⟩

/-- The honest S1932 target and the honest parameterized target have the same
inhabitedness. -/
theorem S1991HonestCFQuotient_nonempty_iff_at
    (l : PrimeGeFive) (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    Nonempty (S1991HonestCFQuotient l A) ↔
      Nonempty (S1991HonestCFQuotientAt l A) := by
  constructor
  · rintro ⟨Q⟩
    exact ⟨Q.toAt⟩
  · rintro ⟨Q⟩
    exact ⟨S1991HonestCFQuotient.ofAt Q⟩

/-- Relabel a legacy S1932 quotient to the honest signature. -/
noncomputable def S1991HonestCFQuotient.ofLegacy {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (Q : S1932CFQuotient l A) : S1991HonestCFQuotient l A where
  cF := S1991Relabel Q.cF S1991HonestCFSignature
    S1991HonestCFSignature_hyperbolic
  cF_signature := rfl
  quotient := S1991InvariantMorphismRelabel S1991HonestCFSignature
    S1991HonestCFSignature_hyperbolic Q.quotient
  quotientWitness := S1991QuotientWitnessRelabel S1991HonestCFSignature
    S1991HonestCFSignature_hyperbolic Q.quotientWitness

/-- Relabel an honest S1932 quotient back to the legacy label. -/
noncomputable def S1991HonestCFQuotient.toLegacy {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (Q : S1991HonestCFQuotient l A) : S1932CFQuotient l A where
  cF := S1991Relabel Q.cF sourceTypeOneOnePlusMinus
    sourceTypeOneOnePlusMinus_hyperbolic
  cF_signature := rfl
  quotient := S1991InvariantMorphismRelabel sourceTypeOneOnePlusMinus
    sourceTypeOneOnePlusMinus_hyperbolic Q.quotient
  quotientWitness := S1991QuotientWitnessRelabel sourceTypeOneOnePlusMinus
    sourceTypeOneOnePlusMinus_hyperbolic Q.quotientWitness

/-- The honest and legacy S1932 targets have the same inhabitedness. -/
theorem S1991HonestCFQuotient_nonempty_iff_legacy
    (l : PrimeGeFive) (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    Nonempty (S1991HonestCFQuotient l A) ↔
      Nonempty (S1991LegacyCFQuotient l A) := by
  constructor
  · rintro ⟨Q⟩
    exact ⟨Q.toLegacy⟩
  · rintro ⟨Q⟩
    exact ⟨S1991HonestCFQuotient.ofLegacy Q⟩

/-- The honest S1932 target is nonempty exactly when the label-free quotient
structure exists. -/
theorem S1991HonestCFQuotient_nonempty_iff_firstMissing
    (l : PrimeGeFive) (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    Nonempty (S1991HonestCFQuotient l A) ↔ S1964FirstMissing l A := by
  rw [S1991HonestCFQuotient_nonempty_iff_at]
  exact S1991HonestCFQuotientAt_nonempty_iff_firstMissing l A

/-! ## 5. The S1886 paper target: honest next to legacy -/

/-- The corrected S1886 paper target: identical to S1886PaperCF except that
C_F carries the honest signature (0; [2,2,2]; 1) instead of the legacy label
(1; [2]; 0). -/
structure S1991HonestPaperCF (l : PrimeGeFive) where
  /-- The coherent {±1} action on the actual S1726 orbicurve. -/
  action : Iut.OrbicurveSignAction S1726Orbicurve
  /-- The quotient orbicurve C_F. -/
  cF : Iut.HyperbolicOrbicurve (S1732A l).F
  /-- The corrected paper signature of C_F. -/
  cF_signature : cF.signature = S1991HonestCFSignature
  /-- The sign-invariant quotient morphism X_F -> C_F. -/
  quotient : Iut.OrbicurveSignInvariantMorphism action cF
  /-- The universal property of the quotient. -/
  quotientWitness : Iut.OrbicurveSignQuotientWitness action quotient

/-- The legacy S1886 paper target, named explicitly for the side-by-side
comparison. -/
abbrev S1991LegacyPaperCF (l : PrimeGeFive) :=
  S1886PaperCF l

/-- Relabel the quotient of a legacy S1886 paper target to the honest
signature.  The sign action is unchanged. -/
noncomputable def S1991HonestPaperCF.ofLegacy {l : PrimeGeFive}
    (Q : S1886PaperCF l) : S1991HonestPaperCF l where
  action := Q.action
  cF := S1991Relabel Q.cF S1991HonestCFSignature
    S1991HonestCFSignature_hyperbolic
  cF_signature := rfl
  quotient := S1991InvariantMorphismRelabel S1991HonestCFSignature
    S1991HonestCFSignature_hyperbolic Q.quotient
  quotientWitness := S1991QuotientWitnessRelabel S1991HonestCFSignature
    S1991HonestCFSignature_hyperbolic Q.quotientWitness

/-- Relabel the quotient of an honest S1886 paper target back to the legacy
label. -/
noncomputable def S1991HonestPaperCF.toLegacy {l : PrimeGeFive}
    (Q : S1991HonestPaperCF l) : S1886PaperCF l where
  action := Q.action
  cF := S1991Relabel Q.cF sourceTypeOneOnePlusMinus
    sourceTypeOneOnePlusMinus_hyperbolic
  cF_signature := rfl
  quotient := S1991InvariantMorphismRelabel sourceTypeOneOnePlusMinus
    sourceTypeOneOnePlusMinus_hyperbolic Q.quotient
  quotientWitness := S1991QuotientWitnessRelabel sourceTypeOneOnePlusMinus
    sourceTypeOneOnePlusMinus_hyperbolic Q.quotientWitness

/-- The honest and legacy S1886 paper targets have the same inhabitedness. -/
theorem S1991HonestPaperCF_nonempty_iff_legacy (l : PrimeGeFive) :
    Nonempty (S1991HonestPaperCF l) ↔
      Nonempty (S1991LegacyPaperCF l) := by
  constructor
  · rintro ⟨Q⟩
    exact ⟨Q.toLegacy⟩
  · rintro ⟨Q⟩
    exact ⟨S1991HonestPaperCF.ofLegacy Q⟩

/-- The honest S1886 target is a coherent sign action together with the
honest S1932 quotient datum. -/
theorem S1991HonestPaperCF_nonempty_iff_exists (l : PrimeGeFive) :
    Nonempty (S1991HonestPaperCF l) ↔
      ∃ A : Iut.OrbicurveSignAction S1726Orbicurve,
        Nonempty (S1991HonestCFQuotient l A) := by
  constructor
  · rintro ⟨Q⟩
    exact ⟨Q.action, ⟨⟨Q.cF, Q.cF_signature, Q.quotient,
      Q.quotientWitness⟩⟩⟩
  · rintro ⟨A, ⟨Q⟩⟩
    exact ⟨⟨A, Q.cF, Q.cF_signature, Q.quotient, Q.quotientWitness⟩⟩

/-- The honest and legacy S1886 paper targets have the same first field
(existential over the sign action). -/
theorem S1991HonestPaperCF_nonempty_iff_legacyExists (l : PrimeGeFive) :
    Nonempty (S1991HonestPaperCF l) ↔
      ∃ A : Iut.OrbicurveSignAction S1726Orbicurve,
        Nonempty (S1932CFQuotient l A) := by
  rw [S1991HonestPaperCF_nonempty_iff_exists]
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A, (S1991HonestCFQuotient_nonempty_iff_legacy l A).mp hA⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, (S1991HonestCFQuotient_nonempty_iff_legacy l A).mpr hA⟩

/-! ## 6. Exact first missing -/

/-- The corrected fixed-action first-missing statement: the existence of the
honest S1932 target. -/
def S1991FirstMissing (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) : Prop :=
  Nonempty (S1991HonestCFQuotient l A)

/-- The corrected paper-level first-missing statement: the existence of the
honest S1886 target. -/
def S1991PaperFirstMissing (l : PrimeGeFive) : Prop :=
  Nonempty (S1991HonestPaperCF l)

/-- The corrected fixed-action target is missing exactly G1, the label-free
quotient structure S1964FirstMissing. -/
theorem S1991FirstMissing_iff_S1964FirstMissing
    (l : PrimeGeFive) (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    S1991FirstMissing l A ↔ S1964FirstMissing l A :=
  S1991HonestCFQuotient_nonempty_iff_firstMissing l A

/-- The corrected fixed-action target is also exactly S1983's [EtTh]-typed
missing statement. -/
theorem S1991FirstMissing_iff_S1983FirstMissing
    (l : PrimeGeFive) (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    S1991FirstMissing l A ↔ S1983FirstMissing l A := by
  rw [S1991FirstMissing]
  rw [S1991HonestCFQuotient_nonempty_iff_at]
  rw [S1991HonestCFQuotientAt_eq_S1983EtThCF l A]
  rw [S1983FirstMissing]

/-- The corrected paper-level target is missing exactly an action together
with G1 for that action. -/
theorem S1991PaperFirstMissing_iff_exists_firstMissing
    (l : PrimeGeFive) :
    S1991PaperFirstMissing l ↔
      ∃ A : Iut.OrbicurveSignAction S1726Orbicurve,
        S1964FirstMissing l A := by
  rw [S1991PaperFirstMissing, S1991HonestPaperCF_nonempty_iff_exists]
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A, (S1991FirstMissing_iff_S1964FirstMissing l A).mp hA⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, (S1991FirstMissing_iff_S1964FirstMissing l A).mpr hA⟩

/-- The corrected paper-level target has the same inhabitedness as the legacy
S1886 first missing (this is the bridge, not an identification of labels). -/
theorem S1991PaperFirstMissing_iff_S1886FirstMissing
    (l : PrimeGeFive) :
    S1991PaperFirstMissing l ↔ S1886FirstMissing l := by
  change Nonempty (S1991HonestPaperCF l) ↔
    Nonempty (S1886PaperCF l)
  exact S1991HonestPaperCF_nonempty_iff_legacy l

/-- G2, recorded as a theorem and not hidden: the honest signature is not
forced by the etale-stack fiber.  For every stack fiber there is a hyperbolic
orbicurve on that fiber whose signature is not (0; [2,2,2]; 1).  Therefore the
honest label in the corrected target is target data; forcing it
geometrically would require changing the production signature field. -/
theorem S1991HonestSignatureNotForcedByFiber {F : Type u} [Field F]
    (fiber : Iut.EtaleStackPseudofunctor F)
    (isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology F)) :
    ∃ X : Iut.HyperbolicOrbicurve F,
      X.stack.fiber = fiber ∧
        X.signature ≠ S1991HonestCFSignature :=
  S1983SignatureNotForcedByFiber fiber isStack

/-- The target-lock decision, recorded as a single theorem: the corrected
signature agrees with S1964/S1983 and differs from the legacy label; the
honest and legacy versions of all three target structures have the same
inhabitedness; and the corrected fixed-action target is exactly G1. -/
theorem S1991TargetLockDecision
    (l : PrimeGeFive) (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    (S1991HonestCFSignature = S1964HonestQuotientSignature) ∧
      (S1991HonestCFSignature = etthSignature EtThType.oneOnePlusMinus) ∧
      (S1991HonestCFSignature ≠ sourceTypeOneOnePlusMinus) ∧
      (Nonempty (S1991HonestCFQuotientAt l A) ↔
        Nonempty (S1991LegacyCFQuotientAt l A)) ∧
      (Nonempty (S1991HonestCFQuotient l A) ↔
        Nonempty (S1932CFQuotient l A)) ∧
      (Nonempty (S1991HonestPaperCF l) ↔
        Nonempty (S1886PaperCF l)) ∧
      (S1991FirstMissing l A ↔ S1964FirstMissing l A) :=
  ⟨S1991HonestCFSignature_eq_S1964HonestQuotientSignature,
    S1991HonestCFSignature_eq_etth,
    S1991HonestCFSignature_ne_legacy,
    S1991HonestCFQuotientAt_nonempty_iff_legacy l A,
    S1991HonestCFQuotient_nonempty_iff_legacy l A,
    S1991HonestPaperCF_nonempty_iff_legacy l,
    S1991FirstMissing_iff_S1964FirstMissing l A⟩

/-! ## 7. Axiom footprint -/

#print axioms S1991HonestCFSignature_eq_S1964HonestQuotientSignature
#print axioms S1991HonestCFSignature_eq_literal
#print axioms S1991HonestCFSignature_data
#print axioms S1991HonestCFSignature_euler
#print axioms S1991HonestCFSignature_euler_eq_legacy
#print axioms S1991HonestCFSignature_hyperbolic
#print axioms S1991HonestCFSignature_ne_legacy
#print axioms S1991LegacyCFSignature_data
#print axioms S1991HonestCFSignature_vs_legacy
#print axioms S1991Relabel
#print axioms S1991InvariantMorphismRelabel
#print axioms S1991QuotientWitnessRelabel
#print axioms S1991CFQuotientAtChangeLabel
#print axioms S1991CFQuotientAt_nonempty_iff_of_label
#print axioms S1991HonestCFQuotientAt_nonempty_iff_legacy
#print axioms S1991CFQuotientAtOfStructure
#print axioms S1991HonestCFQuotientAt_nonempty_iff_firstMissing
#print axioms S1991HonestCFQuotient
#print axioms S1991HonestCFQuotient.toAt
#print axioms S1991HonestCFQuotient.ofAt
#print axioms S1991HonestCFQuotient_nonempty_iff_at
#print axioms S1991HonestCFQuotient.ofLegacy
#print axioms S1991HonestCFQuotient.toLegacy
#print axioms S1991HonestCFQuotient_nonempty_iff_legacy
#print axioms S1991HonestCFQuotient_nonempty_iff_firstMissing
#print axioms S1991HonestPaperCF
#print axioms S1991HonestPaperCF.ofLegacy
#print axioms S1991HonestPaperCF.toLegacy
#print axioms S1991HonestPaperCF_nonempty_iff_legacy
#print axioms S1991HonestPaperCF_nonempty_iff_exists
#print axioms S1991HonestPaperCF_nonempty_iff_legacyExists
#print axioms S1991FirstMissing
#print axioms S1991PaperFirstMissing
#print axioms S1991FirstMissing_iff_S1964FirstMissing
#print axioms S1991FirstMissing_iff_S1983FirstMissing
#print axioms S1991PaperFirstMissing_iff_exists_firstMissing
#print axioms S1991PaperFirstMissing_iff_S1886FirstMissing
#print axioms S1991HonestSignatureNotForcedByFiber
#print axioms S1991TargetLockDecision

end LeanFormal.IUT.XiFPaper.S1991HonestTargetAliasesActual

end
