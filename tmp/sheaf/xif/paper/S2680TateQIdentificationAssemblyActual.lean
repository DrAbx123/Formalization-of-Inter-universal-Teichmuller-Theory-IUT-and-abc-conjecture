import tmp.sheaf.xif.paper.S1493KSideTateTransportActual
import tmp.sheaf.xif.paper.S1515KSideTateRealizesCurveActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4TateQIdentification

/-!
# S2680: conditional D4 Tate-q identification assembly from the actual chain

Consumer: the D4 slot of SourceDefinition31Data (D4ReductionSupply,
SourceDefinition31D4D9Supply.lean line 107) and any downstream consumer of the
frozen boundary TateQIdentificationStatement
(SourceDefinition31D4TateQIdentification.lean).

## What is actually available, and at which level

The actual chain in the tree is:

* S1444 (sectionTateWitness_comparison, sectionFQ, sectionQ, sectionQ_order):
  the F-side clause-(b) comparison at the source-designated A.F-place
  sectionFPlace T b, its q-parameter, and the K-side q-parameter obtained as its
  actual completionMap image, with the order law ord_K(q_K) = e * ord_F(q_F).
* S1493/S1498/S1515: the actual K-side curve transport (S1493CurveTransport:
  canonicalIsElliptic, the transported coordinate change, and the realizesCurve
  equality) from the F-side comparison, plus the exact remaining K-side point
  comparison S1493KPointTransport.

The D4 card BadPlaceTateUniformizationCards P is an F-side object: at every
finite place w of A.F over P.V_mod_bad it requires a q-candidate at w, an actual
TateCurveComparison A.curve w (parameter w hw) (curve over A.F), and prime-to-l
order.  The S1493/S1498 fields live at the A.K-place sectionKPlace T b, with
curve kSideCurve T and parameter sectionQ T b; they have a different type and
cannot fill the card comparison field.  No such transport or shrinking is
performed here.

What does supply the card is the actual F-side clause-(b) comparison family
T.clauseB.q_comparison, which is precisely the per-place Tate comparison input
of Definition 3.1(b); S1444's sectionTateWitness_comparison is its
instantiation at sectionFPlace T b.  The card constructor below is exactly that
unpacking, so it is conditional on the source datum T and introduces no new
hypothesis.  Its value at the section place is definitionally the S1444
comparison (nativeTateUniformizationCard_comparison_sectionFPlace).

The remaining mathematical content of the D4 Tate-q identification is not in
S1493/S1498: it is the equality of the DVR proxy order at the section-chosen
A.K-lift with the actual q order, and the fibre-uniformity of the card orders
over the contraction V(A.F) -> V(A.Fmod).  Both are stated below as explicit
hypotheses, never asserted:

* tateQIdentificationStatement_of_sectionAgreement uses
  sectionFQ T b = proxy order and the fibre uniformity;
* tateQIdentificationStatement_of_sectionQAgreement instead uses the actual
  K-side order sectionQ T b = proxy order (this is the shape in which the
  S1444/S1493/S1498 chain enters, through sectionQ_order) together with
  ramification index one and the fibre uniformity;
* scaledIdentificationStatement_of_sectionQAgreement records the honest scaled
  form before imposing ramification index one.

No sorry, no new axiom, no unconditional F-side comparison, and no instance of
the card or of the identification is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1482KSideTateUniformizationActual
open LeanFormal.IUT.XiFPaper.S1493KSideTateTransportActual
open LeanFormal.IUT.XiFPaper.S1498KSideTateTransportActual
open LeanFormal.IUT.XiFPaper.S1515KSideTateRealizesCurveActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. The actual F-side comparison family and the D4 card -/

/-- The actual clause-(b) Tate comparison witness at a bad A.F-place.  This is
the per-place form of the F-side comparison family (Definition 3.1(b)); S1444's
sectionTateWitness is the special case w = sectionFPlace T b. -/
noncomputable def fSideWitnessAt
    (w : NumberField.FinitePlace T.arithmetic.F)
    (hw : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w ∈
      (nativePlaceSelection T).V_mod_bad) :
    SourceTateComparisonWitness T.arithmetic w :=
  Classical.choice (T.clauseB.q_comparison w hw)

/-- The D4 card, constructed from the actual F-side clause-(b) comparison family.
This is conditional on the source datum T (its clauseB is the source input of
Definition 3.1(b)); no comparison is invented. -/
noncomputable def nativeTateUniformizationCard :
    BadPlaceTateUniformizationCards (nativePlaceSelection T) where
  parameter w hw := (fSideWitnessAt T w hw).parameter
  comparison w hw := (fSideWitnessAt T w hw).comparison
  order_coprime w hw := (fSideWitnessAt T w hw).order_coprime

@[simp] theorem nativeTateUniformizationCard_parameter
    (w : NumberField.FinitePlace T.arithmetic.F)
    (hw : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w ∈
      (nativePlaceSelection T).V_mod_bad) :
    (nativeTateUniformizationCard T).parameter w hw =
      (fSideWitnessAt T w hw).parameter :=
  rfl

@[simp] theorem nativeTateUniformizationCard_comparison
    (w : NumberField.FinitePlace T.arithmetic.F)
    (hw : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w ∈
      (nativePlaceSelection T).V_mod_bad) :
    (nativeTateUniformizationCard T).comparison w hw =
      (fSideWitnessAt T w hw).comparison :=
  rfl

@[simp] theorem nativeTateUniformizationCard_order_coprime
    (w : NumberField.FinitePlace T.arithmetic.F)
    (hw : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w ∈
      (nativePlaceSelection T).V_mod_bad) :
    Nat.Coprime ((nativeTateUniformizationCard T).parameter w hw).order
      l.value :=
  (nativeTateUniformizationCard T).order_coprime w hw

/-! ## 2. The card read off the actual source clause (b)

The card and the clause-(b) comparison family have exactly the same content.
The forward direction uses BadPlaceTateUniformizationCards.witness; the reverse
direction uses choice on the supplied witnesses. -/

theorem nonempty_nativeTateUniformizationCard_iff_clauseB :
    Nonempty (BadPlaceTateUniformizationCards (nativePlaceSelection T)) ↔
      ∀ (w : NumberField.FinitePlace T.arithmetic.F)
        (hw : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w ∈
          (nativePlaceSelection T).V_mod_bad),
        Nonempty (SourceTateComparisonWitness T.arithmetic w) := by
  constructor
  · rintro ⟨C⟩ w hw
    exact ⟨C.witness w hw⟩
  · intro h
    exact ⟨{ parameter := fun w hw => (Classical.choice (h w hw)).parameter
             comparison := fun w hw => (Classical.choice (h w hw)).comparison
             order_coprime := fun w hw => (Classical.choice (h w hw)).order_coprime }⟩

/-! ## 3. The actual S1444 comparison at the source-designated place

The card value at sectionFPlace T b is definitionally the S1444
comparison/parameter.  This is the precise sense in which the actual chain feeds
the card. -/

theorem nativeTateUniformizationCard_parameter_sectionFPlace :
    (nativeTateUniformizationCard T).parameter (sectionFPlace T b)
        (sectionFPlace_mem_bad T b) =
      sectionFQ T b :=
  rfl

theorem nativeTateUniformizationCard_comparison_sectionFPlace :
    (nativeTateUniformizationCard T).comparison (sectionFPlace T b)
        (sectionFPlace_mem_bad T b) =
      sectionTateWitness_comparison T b :=
  rfl

theorem nativeTateUniformizationCard_order_coprime_sectionFPlace :
    Nat.Coprime ((nativeTateUniformizationCard T).parameter (sectionFPlace T b)
      (sectionFPlace_mem_bad T b)).order l.value :=
  sectionFQ_order_coprime T b

/-! ## 4. The source q-parameter order card from the actual section q -/

/-- The clause-(c) q-parameter card whose bookkeeping order is the order of the
actual F-side q-parameter at the source-designated F-place.  The residue
coprimality is clause (b)'s residue_characteristic_prime_to_l transported along
fkDescentShadow_comap; the order coprimality is sectionFQ_order_coprime. -/
noncomputable def nativeQParameterCards :
    BadPlaceQParameterCards (nativePlaceSelection T) where
  badResidueCharacteristic_primeToL p hp := by
    have h := T.clauseB.residue_characteristic_prime_to_l
      (fkDescentShadow (nativePlaceSelection T) p)
      (fkDescentShadow_mem (nativePlaceSelection T) p hp)
    rw [fkDescentShadow_comap] at h
    exact h.symm
  sourceQParameterOrder w hw :=
    (sectionFQ T ⟨NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w, hw⟩).order
  sourceQParameterOrder_pos w hw :=
    (sectionFQ T ⟨NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w, hw⟩).order_pos
  sourceQParameterOrder_primeToL w hw :=
    sectionFQ_order_coprime T
      ⟨NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w, hw⟩

/-! ## 5. Order of the card at the shadow of a section lift -/

/-- Change of the membership proof in the clause-(b) choice does not change the
order: both sides are choice of the same clause-(b) proposition at the same
place. -/
theorem nativeTateUniformizationCard_parameter_order_congr
    (p : NumberField.FinitePlace T.arithmetic.F)
    (h1 h2 : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) p ∈
      (nativePlaceSelection T).V_mod_bad) :
    ((nativeTateUniformizationCard T).parameter p h1).order =
      ((nativeTateUniformizationCard T).parameter p h2).order := by
  have h : (nativeTateUniformizationCard T).parameter p h1 =
      (nativeTateUniformizationCard T).parameter p h2 := by
    simp only [nativeTateUniformizationCard, fSideWitnessAt]
  exact congrArg (fun q => q.order) h

/-- At the shadow of a bad moduli place, the card order is the order of the
actual S1444 F-side q-parameter at the corresponding section place. -/
theorem nativeTateUniformizationCard_order_shadow
    (p : NumberField.FinitePlace T.arithmetic.Fmod)
    (hp : p ∈ (nativePlaceSelection T).V_mod_bad) :
    ((nativeTateUniformizationCard T).parameter
      (fkDescentShadow (nativePlaceSelection T) p)
      (fkDescentShadow_mem (nativePlaceSelection T) p hp)).order =
      (sectionFQ T ⟨p, hp⟩).order := by
  rw [← nativeTateUniformizationCard_parameter_sectionFPlace (T := T) (b := ⟨p, hp⟩)]

/-! ## 6. The order agreement SourceOrderAgreesWithTateCard from fibre
uniformity -/

/-- Fibre uniformity of the card orders over V(A.F) -> V(A.Fmod) yields the
source/Tate-card order agreement for the q-parameter card of section 4.  This is
the exact place where the genuine fibre-uniformity input is consumed. -/
theorem nativeOrderAgreesWithTateCard_of_fiberUniformity
    (hfib : FKDescentFiberUniformityStatement (nativePlaceSelection T)
      (nativeTateUniformizationCard T)) :
    SourceOrderAgreesWithTateCard (nativePlaceSelection T)
      (nativeTateUniformizationCard T) (nativeQParameterCards T) := by
  intro w hw
  have hshadow := nativeTateUniformizationCard_order_shadow (T := T)
    (p := NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w) (hp := hw)
  have hfiber := hfib w
    (fkDescentShadow (nativePlaceSelection T)
      (NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w))
    hw
    (fkDescentShadow_mem (nativePlaceSelection T)
      (NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w) hw)
    (fkDescentShadow_comap (nativePlaceSelection T)
      (NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w)).symm
  exact hshadow.symm.trans hfiber.symm

/-! ## 7. Main conditional assembly through tateQIdentification_of_sourceAgreement -/

/-- The exact remaining order data in the form requested by the tree:
source q-order agreement plus source/Tate-card agreement imply the frozen Tate-q
identification for the card constructed from the actual F-side comparisons. -/
theorem tateQIdentificationStatement_of_agreement
    (Q : BadPlaceQParameterCards (nativePlaceSelection T))
    (hQ : SourceQParameterOrderAgreesWithCandidate (nativePlaceSelection T) Q)
    (hC : SourceOrderAgreesWithTateCard (nativePlaceSelection T)
      (nativeTateUniformizationCard T) Q) :
    TateQIdentificationStatement (nativePlaceSelection T)
      (nativeTateUniformizationCard T) :=
  tateQIdentification_of_sourceAgreement (nativePlaceSelection T)
    (nativeTateUniformizationCard T) Q hQ hC

/-- Conditional D4 Tate-q identification from the actual F-side section q.  The
two hypotheses are exactly the missing identification content: the DVR proxy
order at the section lift equals the actual F-side q order (sectionFQ T b), and
the card orders are constant along the moduli fibres.  Both are stated, not
asserted. -/
theorem tateQIdentificationStatement_of_sectionAgreement
    (hagree : ∀ b : Bad (nativePlaceSelection T),
      (sectionFQ T b).order =
        (badPlaceQCandidate (nativePlaceSelection T) b).order)
    (hfib : FKDescentFiberUniformityStatement (nativePlaceSelection T)
      (nativeTateUniformizationCard T)) :
    TateQIdentificationStatement (nativePlaceSelection T)
      (nativeTateUniformizationCard T) :=
  tateQIdentificationStatement_of_agreement (T := T)
    (nativeQParameterCards T)
    (fun w hw =>
      hagree ⟨NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w, hw⟩)
    (nativeOrderAgreesWithTateCard_of_fiberUniformity (T := T) hfib)

/-- Exact shadow form: on the section agreement and fibre uniformity, the card
order at the shadow of every bad moduli place is the proxy order.  This is the
FKDescentShadowStatement fragment of the identification. -/
theorem fkDescentShadowStatement_nativeCard_of_sectionAgreement
    (hagree : ∀ b : Bad (nativePlaceSelection T),
      (sectionFQ T b).order =
        (badPlaceQCandidate (nativePlaceSelection T) b).order) :
    FKDescentShadowStatement (nativePlaceSelection T)
      (nativeTateUniformizationCard T) := by
  intro w hw
  exact (nativeTateUniformizationCard_order_shadow (T := T)
    (p := NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w) (hp := hw)).trans
    (hagree ⟨NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w, hw⟩)

/-! ## 8. The actual K-side chain (S1444/S1493/S1498/S1515) and the scaled form

sectionQ is the actual completionMap image of sectionFQ at the
source-designated A.K-place (S1444).  Its order law
sectionQ_order : ord_K(q_K) = e * ord_F(q_F) is the order-level content of the
actual chain.  On the scaled section agreement (proxy order = actual K-side q
order) and fibre uniformity, the identification holds in the scaled form of
FKDescentScaledIdentificationStatement; imposing ramification index one gives
the unscaled frozen statement. -/

theorem fkDescentScaledShadowStatement_nativeCard_of_sectionQAgreement
    (hQ : ∀ b : Bad (nativePlaceSelection T),
      (badPlaceQCandidate (nativePlaceSelection T) b).order = (sectionQ T b).order) :
    FKDescentScaledShadowStatement (nativePlaceSelection T)
      (nativeTateUniformizationCard T) := by
  intro w hw
  have hq := hQ ⟨NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w, hw⟩
  have hs := sectionQ_order (T := T)
    (b := ⟨NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w, hw⟩)
  have hc := nativeTateUniformizationCard_order_shadow (T := T)
    (p := NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w) (hp := hw)
  rw [hq, hs, hc]

theorem scaledIdentificationStatement_of_sectionQAgreement
    (hQ : ∀ b : Bad (nativePlaceSelection T),
      (badPlaceQCandidate (nativePlaceSelection T) b).order = (sectionQ T b).order)
    (hfib : FKDescentFiberUniformityStatement (nativePlaceSelection T)
      (nativeTateUniformizationCard T)) :
    FKDescentScaledIdentificationStatement (nativePlaceSelection T)
      (nativeTateUniformizationCard T) :=
  fkDescent_scaledIdentification_of_fiberUniformity (nativePlaceSelection T)
    (nativeTateUniformizationCard T) hfib
    (fkDescentScaledShadowStatement_nativeCard_of_sectionQAgreement (T := T) hQ)

/-- Unscaled frozen identification from the actual K-side section q order, under
ramification index one everywhere. -/
theorem tateQIdentificationStatement_of_sectionQAgreement
    (hQ : ∀ b : Bad (nativePlaceSelection T),
      (badPlaceQCandidate (nativePlaceSelection T) b).order = (sectionQ T b).order)
    (hram : ∀ p : NumberField.FinitePlace T.arithmetic.Fmod,
      fkDescentSectionRamificationIndex (nativePlaceSelection T) p = 1)
    (hfib : FKDescentFiberUniformityStatement (nativePlaceSelection T)
      (nativeTateUniformizationCard T)) :
    TateQIdentificationStatement (nativePlaceSelection T)
      (nativeTateUniformizationCard T) :=
  (fkDescent_tateQIdentification_iff_scaled_of_ramificationIdx_eq_one
    (nativePlaceSelection T) (nativeTateUniformizationCard T) hram).mpr
    (scaledIdentificationStatement_of_sectionQAgreement (T := T) hQ hfib)

/-! ## 9. The exact K-side comparison assembled from S1493/S1498

This is what the actual transport chain supplies: a comparison at the A.K-place
sectionKPlace T b, not at an A.F-place.  It is therefore recorded separately and
is not inserted into the D4 card. -/

noncomputable def kSideComparisonOfTransport
    (hF : S1493CurveTransport T b)
    (hP : S1493KPointTransport T b) :
    TateCurveComparison (kSideCurve (T := T)) (sectionKPlace T b) (sectionQ T b) where
  canonicalIsElliptic := hF.canonicalIsElliptic
  coordinateChange := hF.coordinateChange
  realizesCurve := hF.realizesCurve
  points := hP

theorem kSideComparisonOfTransport_realizesCurve
    (hF : S1493CurveTransport T b)
    (hP : S1493KPointTransport T b) :
    (kSideComparisonOfTransport (T := T) (b := b) hF hP).coordinateChange •
        TateCurve.weierstrassCurve (Completion (sectionKPlace T b)) (sectionQ T b).q =
      ((kSideCurve (T := T)).baseChange (Completion (sectionKPlace T b))).curve :=
  (kSideComparisonOfTransport (T := T) (b := b) hF hP).realizesCurve

/-- The same K-side comparison from the actual (unconditional) transport
 s1493CurveTransport and the exact remaining point transport. -/
theorem kSideComparisonOfActualTransport
    (hP : S1493KPointTransport T b) :
    Nonempty (TateCurveComparison (kSideCurve (T := T)) (sectionKPlace T b) (sectionQ T b)) :=
  ⟨kSideComparisonOfTransport (T := T) (b := b) (s1493CurveTransport T b) hP⟩

/-- Conditional S1482 K-side Tate data from the explicit curve transport hF and
the missing K-side point comparison.  This is the exact content of the S1493/S1498
chain; it is a K-side object, not the F-side D4 card. -/
noncomputable def kSideTateDataOfTransport
    (hF : S1493CurveTransport T b)
    (hP : S1493KPointTransport T b) :
    S1482KSideTateData T b where
  canonicalIsElliptic := hF.canonicalIsElliptic
  coordinateChange := hF.coordinateChange
  realizesCurve := hF.realizesCurve
  points := hP

/-! ## 10. Consumer form -/

theorem badPlaceQProxy_eq_of_nativeIdentification
    (h : TateQIdentificationStatement (nativePlaceSelection T)
      (nativeTateUniformizationCard T))
    (w : NumberField.FinitePlace T.arithmetic.F)
    (hw : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w ∈
      (nativePlaceSelection T).V_mod_bad) :
    badPlaceQProxy (nativePlaceSelection T)
        ⟨NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w, hw⟩ =
      ((NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w) : Nat) : Real)⁻¹ ^
        ((nativeTateUniformizationCard T).parameter w hw).order :=
  badPlaceQProxy_eq_of_identification (nativePlaceSelection T)
    (nativeTateUniformizationCard T) h w hw

end LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual

end

#print axioms LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual.nativeTateUniformizationCard
#print axioms LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual.nonempty_nativeTateUniformizationCard_iff_clauseB
#print axioms LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual.nativeOrderAgreesWithTateCard_of_fiberUniformity
#print axioms LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual.tateQIdentificationStatement_of_agreement
#print axioms LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual.tateQIdentificationStatement_of_sectionAgreement
#print axioms LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual.scaledIdentificationStatement_of_sectionQAgreement
#print axioms LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual.tateQIdentificationStatement_of_sectionQAgreement
#print axioms LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual.kSideComparisonOfTransport
#print axioms LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual.kSideComparisonOfActualTransport
#print axioms LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual.kSideTateDataOfTransport
#print axioms LeanFormal.IUT.XiFPaper.S2680TateQIdentificationAssemblyActual.badPlaceQProxy_eq_of_nativeIdentification
