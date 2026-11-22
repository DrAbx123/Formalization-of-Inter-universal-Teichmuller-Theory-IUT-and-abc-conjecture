import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteCertificateBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CardQCMPComparison
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSHETransportLaws
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.APT
import LeanFormal.IUT.IUTIII.Theorem311.SourcePolyIsoTransportLaws
import LeanFormal.IUT.IUTIII.Theorem311.MultiradialOutputKernel
import LeanFormal.IUT.Audit.Status

/-!
# Wiring the landed Step-XI supplies into `FiniteStepXILinkEvidence`

This module feeds the link-evidence structure of `FiniteCertificateBridge.lean`
(id `IUT-III.finite-certificate-to-contract`) from the landed conditional
assembly cards.  Every remaining source-facing input stays an explicit
hypothesis or a parameterized port; nothing is closed by a trivial proposition
and no existence is asserted.

* **Card-QCMP** (`CardQCMPComparison.lean`): the two real comparison faces
  `q_le_target` and `target_le_theta` of `QCMPComparisonSupply` are consumed
  through their own fields; the two cross-card alignment sockets (certificate
  scalar vs. the object-level signed q-log; QCMP theta scale vs. certificate
  theta scale) are explicit named hypotheses -- neither card implies them.
* **Card-AMPL** (`CardAMPLThetaBoundSupply.lean`): the certificate and its
  `thetaSigned = S.theta` slot alignment come from the AMPL card
  (`certificate` / `certificate_thetaSigned`); the QCMP theta socket is stated
  directly against `S.theta`.
* **Card-IPL** (`SourcePolyIsoTransportLaws.lean`): the (IPL) slot proposition
  is the landed exchange-shape bundle `CardIPLExchangeShape L E`, and its
  evidence is constructed by `cardIPLExchangeShape` from a shell and a
  discharged supply -- conditional on those parameters, this is the one link
  face whose evidence is constructively available.
* **(SHE)/(APT) slots**: not landed as source statements; carried as explicit
  `Prop` and evidence parameters, exactly as in the existing consumers
  (`CertificateHullWiring.lean`, `iqHullLinkEvidence`).

Paper anchors: IUT III, Corollary 3.12, proof, Step (xi) (the link data list
(xi-b), focused extract lines 1032--1034); Remark 3.11.1, (iii) (IPL, pagewise
9850--9865, 9869--9878), (iv) (APT, pagewise 9931--9938; HIS, 9947--9958).
-/

namespace LeanFormal.IUT

noncomputable section

namespace StepXILinkWiring

/-! ## 1. Card-QCMP comparison faces into the link evidence -/

/-- Link evidence over a certificate whose two comparison faces are read from a
Card-QCMP supply: `targetSigned := S.targetSigned`, `q_le_target` is the
supply's own `q_le_target` composed with the scalar alignment socket
`hq_align`, and `target_le_theta` is the supply's own `target_le_theta`
composed with the theta alignment socket `hth`.

The two sockets are the exact cross-card identifications that neither card
proves.  For certificates built by
`StepXIFiniteCertificate.ofAbsoluteDegreeNormalizedSignedLog`
(`ContractSourceReduction.lean`) the scalar socket is definitional
(`le_rfl`); for Card-AMPL certificates see `linkEvidenceOfAMPLQCMP`. -/
def linkEvidenceOfQCMP {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (hq_align : certificate.qSigned ≤
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        S.selectedLowerPlaces S.parameters)
    (hth : S.thetaSigned ≤ certificate.thetaSigned)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence certificate where
  targetSigned := S.targetSigned
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := le_trans hq_align S.q_le_target
  target_le_theta := le_trans S.target_le_theta hth

@[simp] theorem linkEvidenceOfQCMP_targetSigned {k : Type*} [Field k]
    [NumberField k] {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (hq_align : certificate.qSigned ≤
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        S.selectedLowerPlaces S.parameters)
    (hth : S.thetaSigned ≤ certificate.thetaSigned)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    (linkEvidenceOfQCMP S certificate hq_align hth ipl she apt
      hipl hshe hapt).targetSigned = S.targetSigned := rfl

/-- Consumer form: the Cor 3.12 ordered conclusion for the QCMP-wired
contract, through the existing `cor312_of_finite_certificate` assembly. -/
theorem cor312Conclusion_of_QCMPLinkEvidence {k : Type*} [Field k]
    [NumberField k] {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (hq_align : certificate.qSigned ≤
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        S.selectedLowerPlaces S.parameters)
    (hth : S.thetaSigned ≤ certificate.thetaSigned)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      (certificate.toContract
        (linkEvidenceOfQCMP S certificate hq_align hth ipl she apt
          hipl hshe hapt)) :=
  cor312_of_finite_certificate certificate _

/-! ## 2. Card-AMPL certificate junction -/

/-- Link evidence over the Card-AMPL certificate: the certificate is
`CardAMPLThetaBoundSupply.certificate` (`hull_le_theta` slot aligned by the
card), and the QCMP theta socket is stated directly against the supply's
`theta` -- definitionally the certificate's theta through
`certificate_thetaSigned`.  This is the QCMP-parametrized target route,
alternative to the hull-pinned route `finiteLinkEvidenceOfHullTarget` /
`CardAMPLThetaBoundSupply.linkEvidence`. -/
def linkEvidenceOfAMPLQCMP {k : Type*} [Field k] [NumberField k]
    {X : Type*} {W : IQHullLogVolumeInterface X}
    {label : Type*} [Fintype label]
    (S_ampl : CardAMPLThetaBoundSupply W) (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (q : ℝ) (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet) (hqneg : q < 0)
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (hq_align :
      (S_ampl.certificate pt hpt data hvalue hw q hq hqneg).qSigned ≤
        ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
          S.selectedLowerPlaces S.parameters)
    (hth : S.thetaSigned ≤ S_ampl.theta)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence
      (S_ampl.certificate pt hpt data hvalue hw q hq hqneg) :=
  linkEvidenceOfQCMP S _ hq_align hth ipl she apt hipl hshe hapt

/-- Consumer form of the Card-AMPL junction. -/
theorem cor312Conclusion_of_AMPLQCMP {k : Type*} [Field k] [NumberField k]
    {X : Type*} {W : IQHullLogVolumeInterface X}
    {label : Type*} [Fintype label]
    (S_ampl : CardAMPLThetaBoundSupply W) (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (q : ℝ) (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet) (hqneg : q < 0)
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (hq_align :
      (S_ampl.certificate pt hpt data hvalue hw q hq hqneg).qSigned ≤
        ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
          S.selectedLowerPlaces S.parameters)
    (hth : S.thetaSigned ≤ S_ampl.theta)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((S_ampl.certificate pt hpt data hvalue hw q hq hqneg).toContract
        (linkEvidenceOfAMPLQCMP S_ampl pt hpt data hvalue hw q hq hqneg
          S hq_align hth ipl she apt hipl hshe hapt)) :=
  cor312_of_finite_certificate _ _

/-! ## 3. Card-IPL exchange shape as the (IPL) slot -/

universe u v umon uv upi uG uG' uG₂ ua ui uOut₁ uOut₂

/-- The (IPL) slot is instantiated by the landed Step (xi-b)/(xi-c) exchange
shape `CardIPLExchangeShape`, with evidence constructed by
`cardIPLExchangeShape` from a shell and a discharged Card-IPL supply.  The
comparison faces come from Card-QCMP as in `linkEvidenceOfQCMP`; the
(SHE)/(APT) slots remain explicit ports. -/
def linkEvidenceOfQCMPWithIPL {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (hq_align : certificate.qSigned ≤
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        S.selectedLowerPlaces S.parameters)
    (hth : S.thetaSigned ≤ certificate.thetaSigned)
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : MultiradialKernel.Core Label Choice}
    (L : Theorem311Source.PolyIsoTransport.LinkSpan core1 core2)
    (E : Theorem311Source.PolyIsoTransport.CardIPLTransportSupply L)
    (she apt : Prop) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence certificate :=
  linkEvidenceOfQCMP S certificate hq_align hth
    (Theorem311Source.PolyIsoTransport.CardIPLExchangeShape L E) she apt
    (Theorem311Source.PolyIsoTransport.cardIPLExchangeShape L E) hshe hapt

/-- Consumer form of the Card-IPL-wired link evidence. -/
theorem cor312Conclusion_of_QCMPWithIPL {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (hq_align : certificate.qSigned ≤
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        S.selectedLowerPlaces S.parameters)
    (hth : S.thetaSigned ≤ certificate.thetaSigned)
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : MultiradialKernel.Core Label Choice}
    (L : Theorem311Source.PolyIsoTransport.LinkSpan core1 core2)
    (E : Theorem311Source.PolyIsoTransport.CardIPLTransportSupply L)
    (she apt : Prop) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      (certificate.toContract
        (linkEvidenceOfQCMPWithIPL S certificate hq_align hth L E she apt
          hshe hapt)) :=
  cor312_of_finite_certificate certificate _

/-! ## 4. Non-degenerate (strict) upgrade of the two conditional alignment slots -/

/-- Non-degenerate strict alignment package for the five-slot chain
`qSigned < qlog S < targetSigned < thetaSigned < certificate.thetaSigned`:
the two cross-card sockets in strict form, plus the strict separation of the
supply's own two scalar faces.  The two middle fields have no conditional
counterpart in this file (the non-strict faces live inside `S` as
`q_le_target` / `target_le_theta`); they are the minimal added slots,
inhabited on the Q(i)-at-5 test carrier by
`FiniteAlignmentStrictSocketInstance.lean` (id
`IUT-III.finite-alignment-strict-socket-instance`).  This is a field-level
test-carrier shape, NOT a source-level identification of the sockets. -/
structure StrictAlignmentSockets {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label) : Prop where
  /-- First socket, strict: certificate scalar below the object-level signed
  q-log. -/
  q_align_strict : certificate.qSigned <
    ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      S.selectedLowerPlaces S.parameters
  /-- Middle separation of the supply's own chain, strict. -/
  qlog_lt_target :
    ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      S.selectedLowerPlaces S.parameters < S.targetSigned
  /-- Middle separation of the supply's own chain, strict. -/
  target_lt_theta : S.targetSigned < S.thetaSigned
  /-- Second socket, strict: supply theta below the certificate theta. -/
  theta_align_strict : S.thetaSigned < certificate.thetaSigned

/-- The package read as the strict five-slot chain. -/
theorem StrictAlignmentSockets.strictChain {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    {S : StepXIQCMP.QCMPComparisonSupply k}
    {certificate : StepXIFiniteCertificate label}
    (A : StrictAlignmentSockets S certificate) :
    certificate.qSigned <
        ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
          S.selectedLowerPlaces S.parameters ∧
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
          S.selectedLowerPlaces S.parameters < S.targetSigned ∧
      S.targetSigned < S.thetaSigned ∧
      S.thetaSigned < certificate.thetaSigned :=
  ⟨A.q_align_strict, A.qlog_lt_target, A.target_lt_theta,
    A.theta_align_strict⟩

/-- Non-degenerate upgrade of `linkEvidenceOfQCMP`: with a strict alignment
package the two conditional slots are supplied outright. -/
def linkEvidenceOfQCMPOfStrictAlignment {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (A : StrictAlignmentSockets S certificate)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence certificate :=
  linkEvidenceOfQCMP S certificate (le_of_lt A.q_align_strict)
    (le_of_lt A.theta_align_strict) ipl she apt hipl hshe hapt

/-- Consumer form of the non-degenerate upgrade. -/
theorem cor312Conclusion_of_QCMPOfStrictAlignment {k : Type*} [Field k]
    [NumberField k] {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (A : StrictAlignmentSockets S certificate)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      (certificate.toContract
        (linkEvidenceOfQCMPOfStrictAlignment S certificate A ipl she apt
          hipl hshe hapt)) :=
  cor312_of_finite_certificate certificate _

/-- Non-degenerate upgrade of `linkEvidenceOfQCMPWithIPL`: with a strict
alignment package the two conditional slots are supplied outright; the (IPL)
slot remains the landed exchange shape. -/
def linkEvidenceOfQCMPWithIPLOfStrictAlignment {k : Type*} [Field k]
    [NumberField k] {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (A : StrictAlignmentSockets S certificate)
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : MultiradialKernel.Core Label Choice}
    (L : Theorem311Source.PolyIsoTransport.LinkSpan core1 core2)
    (E : Theorem311Source.PolyIsoTransport.CardIPLTransportSupply L)
    (she apt : Prop) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence certificate :=
  linkEvidenceOfQCMPWithIPL S certificate (le_of_lt A.q_align_strict)
    (le_of_lt A.theta_align_strict) L E she apt hshe hapt

/-- Consumer form of the Card-IPL non-degenerate upgrade. -/
theorem cor312Conclusion_of_QCMPWithIPLOfStrictAlignment {k : Type*} [Field k]
    [NumberField k] {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (A : StrictAlignmentSockets S certificate)
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : MultiradialKernel.Core Label Choice}
    (L : Theorem311Source.PolyIsoTransport.LinkSpan core1 core2)
    (E : Theorem311Source.PolyIsoTransport.CardIPLTransportSupply L)
    (she apt : Prop) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      (certificate.toContract
        (linkEvidenceOfQCMPWithIPLOfStrictAlignment S certificate A L E she apt
          hshe hapt)) :=
  cor312_of_finite_certificate certificate _



/-! ## 5. (SHE) slot filled by the landed simultaneity square (reading A) -/

/-- The identity-legs Card-SHE square on any F-prime-strip: the four legs are
the identity links of one strip, so both composite expressions are the shared
two-fold identity link and the commutativity is `rfl`.  Degenerate test witness
for the landed interface `SourceSimultaneousHolomorphicExpression` (id
`IUT-III.source-SHE-simultaneity-exchange`): it shows the slot shape is
inhabited and drives the reading-A consumers below.  It is NOT the source
simultaneity square (the Kummer/evaluation legs remain the open DSH-F gap S2)
and it is NOT the finite model `FiniteSHESquare` (different statement type,
DSH-F trap A3/S5). -/
def identityLegsSquare {V : Type uv} (F : FPrimeStrip.{umon, uv, upi} V) :
    SourceSimultaneousHolomorphicExpression F F F F
      (FPrimeStripLink.refl F) (FPrimeStripLink.refl F)
      (FPrimeStripLink.refl F) (FPrimeStripLink.refl F) :=
  SourceSimultaneousHolomorphicExpression.ofCommutingLegs rfl

/-- The identity-legs square is evidence for its own (SHE) statement. -/
theorem identityLegsSquare_sheStatement {V : Type uv}
    (F : FPrimeStrip.{umon, uv, upi} V) :
    (identityLegsSquare F).sheStatement :=
  (identityLegsSquare F).simultaneous

section SHEAndAPTStatementFill

variable {V : Type uv} {F₁ F₂ F₃ F₄ : FPrimeStrip.{umon, uv, upi} V}
variable {uH : FPrimeStripLink F₁ F₂} {lH : FPrimeStripLink F₃ F₄}
variable {lK : FPrimeStripLink F₁ F₃} {rK : FPrimeStripLink F₂ F₄}

/-- Non-degenerate alignment upgrade with the (SHE) slot filled by reading A:
the slot content is the landed simultaneity square`s own statement
`Eshe.sheStatement` (links level, `domainExpression = codomainExpression`) and
the evidence is the square`s `simultaneous` field, so the (SHE) slot is no
longer an arbitrary supplied `Prop` + proof but is pinned to the landed
statement (`SourceSHETransportLaws`).  A consumer holding the assembled supply
`W : SourceSHESquareSupply G A B C D` passes `W.square` for `Eshe`.  The (APT)
slot remains an explicit parameterized port here. -/
def linkEvidenceOfQCMPWithIPLAndSHEOfStrictAlignment
    {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (A : StrictAlignmentSockets S certificate)
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : MultiradialKernel.Core Label Choice}
    (L : Theorem311Source.PolyIsoTransport.LinkSpan core1 core2)
    (E : Theorem311Source.PolyIsoTransport.CardIPLTransportSupply L)
    (Eshe : SourceSimultaneousHolomorphicExpression F₁ F₂ F₃ F₄ uH lH lK rK)
    (apt : Prop) (hapt : apt) :
    FiniteStepXILinkEvidence certificate :=
  linkEvidenceOfQCMPWithIPL S certificate (le_of_lt A.q_align_strict)
    (le_of_lt A.theta_align_strict) L E Eshe.sheStatement apt
    Eshe.simultaneous hapt

/-- The (SHE) slot of the filled link evidence is the square`s statement
(definitional). -/
@[simp] theorem linkEvidenceOfQCMPWithIPLAndSHEOfStrictAlignment_she
    {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (A : StrictAlignmentSockets S certificate)
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : MultiradialKernel.Core Label Choice}
    (L : Theorem311Source.PolyIsoTransport.LinkSpan core1 core2)
    (E : Theorem311Source.PolyIsoTransport.CardIPLTransportSupply L)
    (Eshe : SourceSimultaneousHolomorphicExpression F₁ F₂ F₃ F₄ uH lH lK rK)
    (apt : Prop) (hapt : apt) :
    (linkEvidenceOfQCMPWithIPLAndSHEOfStrictAlignment S certificate A L E
        Eshe apt hapt).she =
      Eshe.sheStatement :=
  rfl

/-- Consistency with the landed (xi-b) transport
`SourceSimultaneousHolomorphicExpression.sheSlot_evidence`
(`SourceSHETransportLaws.lean`): for the assembled contract the named-slot
transport reproduces exactly the stored (SHE) evidence. -/
theorem sheSlot_evidence_of_QCMPWithIPLAndSHEOfStrictAlignment
    {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (A : StrictAlignmentSockets S certificate)
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : MultiradialKernel.Core Label Choice}
    (L : Theorem311Source.PolyIsoTransport.LinkSpan core1 core2)
    (E : Theorem311Source.PolyIsoTransport.CardIPLTransportSupply L)
    (Eshe : SourceSimultaneousHolomorphicExpression F₁ F₂ F₃ F₄ uH lH lK rK)
    (apt : Prop) (hapt : apt) :
    Eshe.sheSlot_evidence
        (show (certificate.toContract
            (linkEvidenceOfQCMPWithIPLAndSHEOfStrictAlignment S certificate
              A L E Eshe apt hapt)).she = Eshe.sheStatement from rfl) =
      (certificate.toContract
        (linkEvidenceOfQCMPWithIPLAndSHEOfStrictAlignment S certificate
          A L E Eshe apt hapt)).she_evidence :=
  rfl

/-- Consumer form of the reading-A (SHE) fill. -/
theorem cor312Conclusion_of_QCMPWithIPLAndSHEOfStrictAlignment
    {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (A : StrictAlignmentSockets S certificate)
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : MultiradialKernel.Core Label Choice}
    (L : Theorem311Source.PolyIsoTransport.LinkSpan core1 core2)
    (E : Theorem311Source.PolyIsoTransport.CardIPLTransportSupply L)
    (Eshe : SourceSimultaneousHolomorphicExpression F₁ F₂ F₃ F₄ uH lH lK rK)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (certificate.toContract
        (linkEvidenceOfQCMPWithIPLAndSHEOfStrictAlignment S certificate
          A L E Eshe apt hapt)) :=
  cor312_of_finite_certificate certificate _

variable {l : PrimeGeFive} {V₀ : Type uv}
variable {G₁ : Type uG} [Group G₁] {G₁' : Type uG'} [Group G₁']
variable {G₂ : Type uG₂} [Group G₂]
variable {I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V₀}
variable {n n' : Int} {Output₁ : Type uOut₁} {Output₂ : Type uOut₂}
variable {S₀ : Theorem311Source.SourceOneColumnArithmeticHolomorphicStructure V₀}
variable {A₁ : Theorem311Source.SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁}
variable {A₂ : Theorem311Source.SourceTheorem311MultiradialAlgorithm G₁' G₂ I n' Output₂}

/-- (SHE)+ (APT) fill: in addition to the reading-A (SHE) fill above, the
(APT) slot is pinned to the landed statement `SourceAPTStatement S₀ A₁ A₂`
(`APT.lean`, id `IUT-III.source-algorithmic-parallel-transport`) with the
supplied transport witness as evidence.  The witness is the pending card
`IUT-III.source-APT-transport-supply`; this fill constructs nothing. -/
def linkEvidenceOfQCMPWithIPLAndSHEAndAPTOfStrictAlignment
    {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (A : StrictAlignmentSockets S certificate)
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : MultiradialKernel.Core Label Choice}
    (L : Theorem311Source.PolyIsoTransport.LinkSpan core1 core2)
    (E : Theorem311Source.PolyIsoTransport.CardIPLTransportSupply L)
    (Eshe : SourceSimultaneousHolomorphicExpression F₁ F₂ F₃ F₄ uH lH lK rK)
    (transport : Theorem311Source.SourceAPTStatement S₀ A₁ A₂) :
    FiniteStepXILinkEvidence certificate :=
  linkEvidenceOfQCMPWithIPLAndSHEOfStrictAlignment S certificate A L E Eshe
    (Theorem311Source.SourceAPTStatement S₀ A₁ A₂) transport

/-- The (APT) slot of the filled link evidence is the landed statement
(definitional). -/
@[simp] theorem linkEvidenceOfQCMPWithIPLAndSHEAndAPTOfStrictAlignment_apt
    {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (A : StrictAlignmentSockets S certificate)
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : MultiradialKernel.Core Label Choice}
    (L : Theorem311Source.PolyIsoTransport.LinkSpan core1 core2)
    (E : Theorem311Source.PolyIsoTransport.CardIPLTransportSupply L)
    (Eshe : SourceSimultaneousHolomorphicExpression F₁ F₂ F₃ F₄ uH lH lK rK)
    (transport : Theorem311Source.SourceAPTStatement S₀ A₁ A₂) :
    (linkEvidenceOfQCMPWithIPLAndSHEAndAPTOfStrictAlignment S certificate A L E
        Eshe transport).apt =
      Theorem311Source.SourceAPTStatement S₀ A₁ A₂ :=
  rfl

/-- Consistency with the landed (APT)-slot transport
`SourceAPTSlotAssembly.aptSlot_evidence` (`APT.lean`): the named-slot
transport reproduces exactly the stored (APT) evidence. -/
theorem aptSlot_evidence_of_QCMPWithIPLAndSHEAndAPTOfStrictAlignment
    {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (A : StrictAlignmentSockets S certificate)
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : MultiradialKernel.Core Label Choice}
    (L : Theorem311Source.PolyIsoTransport.LinkSpan core1 core2)
    (E : Theorem311Source.PolyIsoTransport.CardIPLTransportSupply L)
    (Eshe : SourceSimultaneousHolomorphicExpression F₁ F₂ F₃ F₄ uH lH lK rK)
    (transport : Theorem311Source.SourceAPTStatement S₀ A₁ A₂) :
    Theorem311Source.SourceAPTSlotAssembly.aptSlot_evidence
        ({ contract :=
            certificate.toContract
              (linkEvidenceOfQCMPWithIPLAndSHEAndAPTOfStrictAlignment S
                certificate A L E Eshe transport)
           slot_identifies := rfl } :
          Theorem311Source.SourceAPTSlotAssembly S₀ A₁ A₂)
        transport =
      (certificate.toContract
        (linkEvidenceOfQCMPWithIPLAndSHEAndAPTOfStrictAlignment S certificate
          A L E Eshe transport)).apt_evidence :=
  rfl

/-- Consumer form of the (SHE)+ (APT) fill. -/
theorem cor312Conclusion_of_QCMPWithIPLAndSHEAndAPTOfStrictAlignment
    {k : Type*} [Field k] [NumberField k]
    {label : Type*} [Fintype label]
    (S : StepXIQCMP.QCMPComparisonSupply k)
    (certificate : StepXIFiniteCertificate label)
    (A : StrictAlignmentSockets S certificate)
    {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : MultiradialKernel.Core Label Choice}
    (L : Theorem311Source.PolyIsoTransport.LinkSpan core1 core2)
    (E : Theorem311Source.PolyIsoTransport.CardIPLTransportSupply L)
    (Eshe : SourceSimultaneousHolomorphicExpression F₁ F₂ F₃ F₄ uH lH lK rK)
    (transport : Theorem311Source.SourceAPTStatement S₀ A₁ A₂) :
    Cor312Conclusion
      (certificate.toContract
        (linkEvidenceOfQCMPWithIPLAndSHEAndAPTOfStrictAlignment S certificate
          A L E Eshe transport)) :=
  cor312_of_finite_certificate certificate _

end SHEAndAPTStatementFill

end StepXILinkWiring

end

namespace Audit

/-- Audit record for the link-evidence wiring. -/
def finiteCertificateLinkEvidenceWiring : Obligation :=
  { id := "IUT-III.finite-certificate-link-evidence-wiring"
    source :=
      "IUT III, Corollary 3.12, proof, Step (xi) (link data list (xi-b)); " ++
        "Remark 3.11.1, (iii) (IPL), (iv) (APT / HIS)"
    status := VerificationStatus.interface
    note :=
      "Wires the landed Step-XI conditional-assembly cards into " ++
        "`FiniteStepXILinkEvidence` (`FiniteCertificateBridge.lean`, id " ++
        "IUT-III.finite-certificate-to-contract).  (1) Comparison faces: " ++
        "`linkEvidenceOfQCMP` consumes the QCMP supply's own `q_le_target` / " ++
        "`target_le_theta` through the two explicit alignment sockets " ++
        "(certificate scalar <= object-level signed q-log; QCMP theta <= " ++
        "certificate theta); neither socket is derivable from the cards.  " ++
        "(2) Card-AMPL junction: `linkEvidenceOfAMPLQCMP` takes the certificate " ++
        "from `CardAMPLThetaBoundSupply.certificate` and states the theta " ++
        "socket directly against `S.theta` (definitional through " ++
        "`certificate_thetaSigned`); a QCMP-parametrized alternative to the " ++
        "hull-pinned `finiteLinkEvidenceOfHullTarget` route.  (3) Card-IPL " ++
        "face: the (IPL) slot is the landed exchange shape " ++
        "`CardIPLExchangeShape`, evidence constructed by `cardIPLExchangeShape` " ++
        "from a shell and a discharged supply (`linkEvidenceOfQCMPWithIPL`).  " ++
        "(4) (SHE)/(APT) slots: explicit parameterized Prop+evidence ports; no " ++
        "landed source statement, no existence asserted.  Headline conclusions " ++
        "`cor312Conclusion_of_QCMPLinkEvidence` / `cor312Conclusion_of_AMPLQCMP` " ++
        "/ `cor312Conclusion_of_QCMPWithIPL` reach `Cor312Conclusion` through " ++
        "the existing `cor312_of_finite_certificate` assembly.  NOT proved: " ++
        "source instantiations of any supply, the two alignment sockets, the " ++
        "(SHE)/(APT) statements, and any numerical conclusion.  (5) " ++
        "Non-degenerate upgrade: `StrictAlignmentSockets` packages the strict " ++
        "five-slot separations (the two internal ones have no conditional " ++
        "counterpart in this file); the `OfStrictAlignment` wrappers supply " ++
        "the two conditional slots outright.  The Q(i)-at-5 strict instance " ++
        "(id `IUT-III.finite-alignment-strict-socket-instance`) inhabits the " ++
        "package on the test carrier; the source-level identification of the " ++
        "sockets remains open.  (6) (SHE) reading-A fill: " ++
        "`linkEvidenceOfQCMPWithIPLAndSHEOfStrictAlignment` replaces the two " ++
        "(SHE) ports by the landed simultaneity-square statement " ++
        "(`SourceSHETransportLaws`): slot content = the square`s `sheStatement`, " ++
        "evidence = its `simultaneous` field; the fill agrees definitionally " ++
        "with the landed transport `sheSlot_evidence` " ++
        "(`sheSlot_evidence_of_QCMPWithIPLAndSHEOfStrictAlignment`, rfl), and " ++
        "`identityLegsSquare` is a degenerate identity-legs test witness only.  " ++
        "(7) (APT) statement fill: " ++
        "`linkEvidenceOfQCMPWithIPLAndSHEAndAPTOfStrictAlignment` pins the (APT) " ++
        "slot to the landed statement `SourceAPTStatement` " ++
        "(`IUT-III.source-algorithmic-parallel-transport`) and consumes a " ++
        "supplied transport witness (pending card " ++
        "`IUT-III.source-APT-transport-supply`), agreeing definitionally with " ++
        "`aptSlot_evidence` (rfl).  Neither fill constructs a source object; " ++
        "per-route supplied-premise counts are recorded in the package report."
    dependsOn :=
      [ "IUT-III.finite-certificate-to-contract",
        "IUT-III.card-qcmp-comparison-supply",
        "IUT-III.card-ampl-theta-bound-supply",
        "IUT-III.card-ipl-poly-iso-transport-laws",
        "IUT-III.source-SHE-simultaneity-exchange",
        "IUT-III.source-algorithmic-parallel-transport" ] }

end Audit

end LeanFormal.IUT
