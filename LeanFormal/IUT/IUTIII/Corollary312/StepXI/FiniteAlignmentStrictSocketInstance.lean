import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteAlignmentSocketInstance
import Mathlib.Tactic

/-!
# Strict (non-degenerate) alignment-socket instance on the Q(i)-at-5 carrier

`FiniteAlignmentSocketInstance.lean` (id `IUT-III.finite-alignment-socket-instance`)
materializes the two alignment sockets of the Cor 3.12 Step (xi) link at the
degenerate collapse point `q = target = theta` (`le_rfl`).  This module removes
the degeneracy at the field level: on the same finite carrier (the Gaussian
field at its concrete place over `5`), the five scalar slots are chosen
pairwise strictly increasing

`certificate.qSigned < qLog < supply.targetSigned < supply.thetaSigned <
certificate.thetaSigned`

and the two sockets are proved in strict form; `linkEvidenceOfQCMPWithIPL` is
again completely inhabited, now with strictly separated slots.

## Frozen claim (stated before the proof)

On the Q(i)-at-5 finite carrier there exists a `FiniteStepXILinkEvidence`
instance built by `linkEvidenceOfQCMPWithIPL` whose five scalar slots are
pairwise strictly increasing, with every separation proved from
`normalizedLowerSignedLog_neg` (`qLog < 0`) plus ordered-ring arithmetic on
unit offsets only: no numerical evaluation of the q-log, no source data.

## Read-only assessment of the Q20 supply layer (result: orthogonal)

`ABCBridge/Bridge/Cor312ComparisonGapSupplyLayer.lean` (SHA256
`B9EED190EC0A8E9DD9E76ED9EE9A6EFF9A883810FE20BC7814ADEED4DA07F479`) supplies
the gap inputs of the Cor 3.12 epsilon-arithmetic comparison on the carrier
`Theorem311Source.OriginalInput l V`, at the ENNReal value level
(`sourceSetVolume`, `sourceHullVolume`, unit-region normalization).  Its `hunit`
face is itself conditional (`SourceUnitRegionHaarData` is additional named
data), and no declaration in the tree links any OriginalInput-layer quantity
to the real scalar `absoluteDegreeNormalizedLowerSignedLog`; the two layers
are orthogonal.  This module therefore does **not** consume the Q20 layer;
the strict instance below is a field-level test-carrier witness.  For the
source-facing line, the missing object is an interface/dictionary between the
q-log scalar face and the OriginalInput value-carrier face; the Q20 wall is a
different wall (hull normalization), not the socket identification.

## Boundary

* Still a finite test-carrier witness: strictness comes from the test
  carrier's scalar freedom (unit offsets), not from any supply layer.
* The source-level identification of the two sockets (the two genuinely
  different source quantities) remains open; nothing here replaces it.
* Non-vacuity strengthened: the socket shape admits strictly separated
  solutions, so no constraint of the shape forces the collapse.
-/

namespace LeanFormal.IUT

noncomputable section

/-- The Gaussian field's defining polynomial is irreducible on this carrier;
local (per-file) by the established convention of the sibling carriers
(ConcreteArithmeticExample.lean, ConcreteFinitePlaceBoundary.lean,
FiniteAlignmentSocketInstance.lean). -/
local instance gaussianPolynomial_irreducible_fact_alignmentStrictSocket :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace StepXILinkWiring

/-! ## 1. Negativity of the carrier q-log -/

/-- The object-level signed q-log of the concrete family is negative
(`normalizedLowerSignedLog_neg` for this carrier). -/
theorem finiteAlignmentQLog_negative : finiteAlignmentQLog < 0 := by
  simpa [finiteAlignmentQLog] using
    ArithmeticQPilotGlobalNormalization.normalizedLowerSignedLog_neg
      finiteAlignmentSelection finiteAlignmentParameters
      finiteAlignmentSelection_nonempty

/-! ## 2. Strict supply and certificate over the same carrier -/

/-- The strict supply: the same place family, with the target and theta scales
moved strictly above the q-log by unit offsets.  Field-level witness;
`target != qLog` and theta takes an independent value. -/
def finiteAlignmentStrictSupply :
    StepXIQCMP.QCMPComparisonSupply GaussianField where
  selectedLowerPlaces := finiteAlignmentSelection
  parameters := finiteAlignmentParameters
  selected_nonempty := finiteAlignmentSelection_nonempty
  targetSigned := finiteAlignmentQLog + 1
  thetaSigned := finiteAlignmentQLog + 2
  q_le_target := by
    change finiteAlignmentQLog ≤ finiteAlignmentQLog + 1
    linarith
  target_le_theta := by linarith

/-- The strict certificate: `qSigned` strictly below the q-log, `thetaSigned`
strictly above the supply theta. -/
def finiteAlignmentStrictCertificate : StepXIFiniteCertificate Unit :=
  StepXIFiniteCertificate.ofHullUniform finiteAlignmentHull
    (finiteAlignmentQLog - 1) (finiteAlignmentQLog + 3)
    (by change finiteAlignmentQLog - 1 ≤ finiteAlignmentQLog; linarith)
    (by change finiteAlignmentQLog ≤ finiteAlignmentQLog + 3; linarith)
    (by linarith [finiteAlignmentQLog_negative])

@[simp] theorem finiteAlignmentStrictSupply_targetSigned :
    finiteAlignmentStrictSupply.targetSigned = finiteAlignmentQLog + 1 := rfl

@[simp] theorem finiteAlignmentStrictSupply_thetaSigned :
    finiteAlignmentStrictSupply.thetaSigned = finiteAlignmentQLog + 2 := rfl

@[simp] theorem finiteAlignmentStrictSupply_qLog :
    ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      finiteAlignmentStrictSupply.selectedLowerPlaces
      finiteAlignmentStrictSupply.parameters = finiteAlignmentQLog := rfl

@[simp] theorem finiteAlignmentStrictCertificate_qSigned :
    finiteAlignmentStrictCertificate.qSigned = finiteAlignmentQLog - 1 := rfl

@[simp] theorem finiteAlignmentStrictCertificate_thetaSigned :
    finiteAlignmentStrictCertificate.thetaSigned = finiteAlignmentQLog + 3 := rfl

/-! ## 3. The two sockets in strict form -/

/-- First socket, strict: the certificate scalar lies strictly below the
object-level signed q-log. -/
theorem finiteAlignmentStrict_socket_q :
    finiteAlignmentStrictCertificate.qSigned <
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        finiteAlignmentStrictSupply.selectedLowerPlaces
        finiteAlignmentStrictSupply.parameters := by
  rw [finiteAlignmentStrictCertificate_qSigned, finiteAlignmentStrictSupply_qLog]
  linarith

/-- Second socket, strict: the supply theta scale lies strictly below the
certificate theta scale. -/
theorem finiteAlignmentStrict_socket_theta :
    finiteAlignmentStrictSupply.thetaSigned <
      finiteAlignmentStrictCertificate.thetaSigned := by
  rw [finiteAlignmentStrictSupply_thetaSigned,
    finiteAlignmentStrictCertificate_thetaSigned]
  linarith

/-- The five scalar slots of the strict instance are pairwise strictly
increasing: no constraint of the socket shape forces the collapse. -/
theorem finiteAlignmentStrict_ordering :
    finiteAlignmentStrictCertificate.qSigned < finiteAlignmentQLog ∧
      finiteAlignmentQLog < finiteAlignmentStrictSupply.targetSigned ∧
      finiteAlignmentStrictSupply.targetSigned <
        finiteAlignmentStrictSupply.thetaSigned ∧
      finiteAlignmentStrictSupply.thetaSigned <
        finiteAlignmentStrictCertificate.thetaSigned := by
  rw [finiteAlignmentStrictCertificate_qSigned,
    finiteAlignmentStrictSupply_targetSigned,
    finiteAlignmentStrictSupply_thetaSigned,
    finiteAlignmentStrictCertificate_thetaSigned]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## 4. Complete inhabitant at the strict point -/

/-- The link evidence at the strict (non-degenerate) point. -/
def finiteAlignmentStrictLinkEvidence :
    FiniteStepXILinkEvidence finiteAlignmentStrictCertificate :=
  linkEvidenceOfQCMPWithIPL finiteAlignmentStrictSupply
    finiteAlignmentStrictCertificate
    (le_of_lt finiteAlignmentStrict_socket_q)
    (le_of_lt finiteAlignmentStrict_socket_theta)
    finiteAlignmentLinkSpan finiteAlignmentIPLSupply
    (ConcreteFiniteStepXI.finiteSHEProposition finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteAPTProposition finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteSHEProposition_proved finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteAPTProposition_proved finiteAlignmentFive 0)

/-- The contract assembled from the strict instance. -/
def finiteAlignmentStrictContract : StepXIContract :=
  finiteAlignmentStrictCertificate.toContract finiteAlignmentStrictLinkEvidence

/-- Headline: the Cor 3.12 ordered conclusion at the strict point, through the
existing consumer `cor312Conclusion_of_QCMPWithIPL`. -/
theorem finiteAlignmentStrictConclusion :
    Cor312Conclusion finiteAlignmentStrictContract :=
  cor312Conclusion_of_QCMPWithIPL finiteAlignmentStrictSupply
    finiteAlignmentStrictCertificate
    (le_of_lt finiteAlignmentStrict_socket_q)
    (le_of_lt finiteAlignmentStrict_socket_theta)
    finiteAlignmentLinkSpan finiteAlignmentIPLSupply
    (ConcreteFiniteStepXI.finiteSHEProposition finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteAPTProposition finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteSHEProposition_proved finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteAPTProposition_proved finiteAlignmentFive 0)

/-! ## 5. Non-degenerate package and the upgraded wiring route -/

/-- The strict five-slot chain as an inhabitation of the wiring file's
`StrictAlignmentSockets` package. -/
theorem finiteAlignmentStrictAlignment :
    StrictAlignmentSockets finiteAlignmentStrictSupply
      finiteAlignmentStrictCertificate :=
  ⟨finiteAlignmentStrict_socket_q,
    by
      rw [finiteAlignmentStrictSupply_qLog,
        finiteAlignmentStrictSupply_targetSigned]
      linarith,
    by
      rw [finiteAlignmentStrictSupply_targetSigned,
        finiteAlignmentStrictSupply_thetaSigned]
      linarith,
    finiteAlignmentStrict_socket_theta⟩

/-- The Cor 3.12 conclusion through the wiring file's non-degenerate upgrade
route `cor312Conclusion_of_QCMPWithIPLOfStrictAlignment`, i.e. with the two
conditional alignment slots discharged by `finiteAlignmentStrictAlignment`. -/
theorem finiteAlignmentStrictConclusionOfStrictAlignment :
    Cor312Conclusion finiteAlignmentStrictContract :=
  cor312Conclusion_of_QCMPWithIPLOfStrictAlignment finiteAlignmentStrictSupply
    finiteAlignmentStrictCertificate finiteAlignmentStrictAlignment
    finiteAlignmentLinkSpan finiteAlignmentIPLSupply
    (ConcreteFiniteStepXI.finiteSHEProposition finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteAPTProposition finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteSHEProposition_proved finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteAPTProposition_proved finiteAlignmentFive 0)


/-! ## 6. Reading-A (SHE) fill on the strict instance -/

/-- The degenerate identity-legs Card-SHE square over the concrete rational
prime-strip `localFPrimeStrip`: the test-carrier witness of the reading-A
(SHE) fill.  Boundary: four identity legs; not the source simultaneity square
(S2 open) and not the finite model `FiniteSHESquare`. -/
def finiteAlignmentSHEIdentitySquare :
    SourceSimultaneousHolomorphicExpression localFPrimeStrip localFPrimeStrip
      localFPrimeStrip localFPrimeStrip
      (FPrimeStripLink.refl localFPrimeStrip)
      (FPrimeStripLink.refl localFPrimeStrip)
      (FPrimeStripLink.refl localFPrimeStrip)
      (FPrimeStripLink.refl localFPrimeStrip) :=
  identityLegsSquare localFPrimeStrip

/-- The strict-instance link evidence with the (SHE) slot filled by the
reading-A identity-legs square statement; the (APT) slot keeps the proved
finite-model proposition. -/
def finiteAlignmentStrictSHESquareLinkEvidence :
    FiniteStepXILinkEvidence finiteAlignmentStrictCertificate :=
  linkEvidenceOfQCMPWithIPLAndSHEOfStrictAlignment finiteAlignmentStrictSupply
    finiteAlignmentStrictCertificate finiteAlignmentStrictAlignment
    finiteAlignmentLinkSpan finiteAlignmentIPLSupply finiteAlignmentSHEIdentitySquare
    (ConcreteFiniteStepXI.finiteAPTProposition finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteAPTProposition_proved finiteAlignmentFive 0)

/-- The contract assembled from the reading-A-filled strict link evidence. -/
def finiteAlignmentStrictSHESquareContract : StepXIContract :=
  finiteAlignmentStrictCertificate.toContract
    finiteAlignmentStrictSHESquareLinkEvidence

/-- Headline: the Cor 3.12 ordered conclusion through the reading-A (SHE)-fill
consumer `cor312Conclusion_of_QCMPWithIPLAndSHEOfStrictAlignment`. -/
theorem finiteAlignmentStrictConclusionWithSHESquare :
    Cor312Conclusion finiteAlignmentStrictSHESquareContract :=
  cor312Conclusion_of_QCMPWithIPLAndSHEOfStrictAlignment
    finiteAlignmentStrictSupply finiteAlignmentStrictCertificate
    finiteAlignmentStrictAlignment finiteAlignmentLinkSpan finiteAlignmentIPLSupply
    finiteAlignmentSHEIdentitySquare
    (ConcreteFiniteStepXI.finiteAPTProposition finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteAPTProposition_proved finiteAlignmentFive 0)

end StepXILinkWiring

end

namespace Audit

/-- The strict (non-degenerate) alignment-socket instance. -/
def finiteAlignmentStrictSocketInstance : Obligation :=
  { id := "IUT-III.finite-alignment-strict-socket-instance"
    source :=
      "IUT III, Corollary 3.12, proof, Step (xi) (link data list (xi-b)); " ++
        "Remark 3.11.1, (iii) (IPL), (iv) (APT / HIS)"
    status := VerificationStatus.testCarrier
    note :=
      "Strict materialization of the two alignment sockets on the Q(i)-at-5 " ++
        "finite test carrier: five scalar slots pairwise strictly increasing " ++
        "(certificate q < q-log < supply target < supply theta < certificate " ++
        "theta), sockets proved in strict form from `normalizedLowerSignedLog_" ++
        "neg` plus unit offsets only; `linkEvidenceOfQCMPWithIPL` fully " ++
        "inhabited.  Read-only assessment recorded: the Q20 supply layer " ++
        "(`ABCBridge/Bridge/Cor312ComparisonGapSupplyLayer.lean`, SHA256 " ++
        "B9EED190...) lives on the `Theorem311Source.OriginalInput` ENNReal " ++
        "value carrier and has no interface to the real q-log scalars; it is " ++
        "orthogonal and is not consumed here.  Boundary: still a finite " ++
        "test-carrier field-level witness; the source-level identification of " ++
        "the two sockets remains open, and no source instantiation is claimed.  " ++
        "The `StrictAlignmentSockets` package of the wiring file is inhabited " ++
        "(`finiteAlignmentStrictAlignment`), and the non-degenerate upgrade " ++
        "consumer `cor312Conclusion_of_QCMPWithIPLOfStrictAlignment` reaches " ++
        "the same contract (`finiteAlignmentStrictConclusionOfStrictAlignment`).  " ++
        "A reading-A (SHE)-filled route is also inhabited on the same carrier: " ++
        "`finiteAlignmentStrictSHESquareLinkEvidence` fills the (SHE) slot by " ++
        "the identity-legs square `finiteAlignmentSHEIdentitySquare` (degenerate " ++
        "test witness; the source square remains open) with the same (APT) " ++
        "finite model, and `finiteAlignmentStrictConclusionWithSHESquare` " ++
        "reaches the conclusion through the fill consumer."
    dependsOn :=
      [ "IUT-III.finite-alignment-socket-instance",
        "IUT-III.finite-certificate-link-evidence-wiring",
        "IUT-III.concrete-finite-stepXI-route",
        "IUT-I.concrete-initial-theta-finite-place-boundary",
        "IUT-III.card-qcmp-comparison-supply" ] }

end Audit

end LeanFormal.IUT
