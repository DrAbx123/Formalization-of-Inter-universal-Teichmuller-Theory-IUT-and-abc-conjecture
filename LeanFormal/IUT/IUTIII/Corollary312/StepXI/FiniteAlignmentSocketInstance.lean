import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteCertificateLinkEvidenceWiring
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ConcreteFiniteRouteColumns
import LeanFormal.IUT.IUTIII.Theorem311.SourcePolyIsoTransportDischarge
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteFinitePlaceBoundary
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import LeanFormal.IUT.Audit.Status

/-!
# Finite alignment-socket instance on the concrete `Q(i)`-at-`5` carrier

`FiniteCertificateLinkEvidenceWiring.lean` (id
`IUT-III.finite-certificate-link-evidence-wiring`) isolates the two cross-card
alignment sockets of the Cor 3.12 Step (xi) link as explicit hypotheses:
`hq_align` (certificate scalar against the object-level signed q-log) and
`hth` (Card-QCMP theta scale against the certificate theta scale).  Neither
socket is implied by the landed cards, and their source-level identification
remains open.

This module materializes both sockets on a fully concrete finite carrier:

* the Gaussian field `GaussianField` at the concrete place over `5`
  (`concreteGaussianFivePlace`) with its DVR q-candidate
  (`NumberFieldFinitePlace.finitePlaceQCandidate_nonempty`);
* the canonical-collapse QCMP supply over that place family
  (`QCMPComparisonSupply.ofCanonicalCollapse`), whose target and theta scales
  are definitionally the object-level signed q-log of the family;
* a uniform hull pinned to the same signed q-log and the certificate
  `StepXIFiniteCertificate.ofAbsoluteDegreeNormalizedSignedLog` over it.

Every scalar in the two sockets is then definitionally the same quantity
`absoluteDegreeNormalizedLowerSignedLog` of the same family, so both sockets
are `le_rfl`: `linkEvidenceOfQCMPWithIPL` is completely inhabited on this
carrier, with the (IPL) slot the landed exchange shape via `trivialSupply`,
the (SHE)/(APT) slots the landed finite propositions of
`ConcreteFiniteRouteColumns.lean`, and the headline `Cor312Conclusion`
reached through the existing consumer `cor312Conclusion_of_QCMPWithIPL`.

## Boundary (deliberately narrow)

* Finite test-carrier instance only: it carries no Theta-link or pilot data,
  and it materializes the sockets at the degenerate collapse point
  `q = target = theta`.  It is NOT a source instantiation of the supply, and
  the non-degenerate source-level alignment identification remains open.
* The test kernel below (trivial action on `Z`/`Unit`) is a scaffold for
  inhabiting the link shell; it is not a source core.  The sibling scaffold
  `SourceColumnCarrierIdentification.trivialCore` was in flight at the time
  of writing and is deliberately not imported.
* The (SHE)/(APT) instantiations are the finite model propositions; their
  source-level statements remain un-landed, as recorded in the wiring card.
-/

namespace LeanFormal.IUT

noncomputable section

local instance gaussianPolynomial_irreducible_fact_alignmentSocket :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace StepXILinkWiring

/-! ## 1. The finite test kernel -/

/-- Scaffold kernel for the finite instance: the trivial action of `Z` on
`Unit` with level `0`.  Inhabits the link shell only; not a source core. -/
def finiteAlignmentTestCore : MultiradialKernel.Core ℤ Unit where
  base := Unit.unit
  level := fun _ => 0
  ind1 := fun _ c => c
  ind2 := fun _ c => c
  ind3 := fun _ c => c
  ind1_zero := fun _ => rfl
  ind1_add := fun _ _ _ => rfl
  ind1_inverse := fun _ _ => rfl
  ind2_zero := fun _ => rfl
  ind2_add := fun _ _ _ => rfl
  ind2_inverse := fun _ _ => rfl
  ind3_zero := fun _ => rfl
  ind3_add := fun _ _ _ => rfl
  ind1_ind2_commute := fun _ _ _ => rfl
  ind1_ind3_commute := fun _ _ _ => rfl
  ind2_ind3_commute := fun _ _ _ => rfl
  ind1_level := fun _ _ => rfl
  ind2_level := fun _ _ => rfl
  ind3_level := fun _ _ => le_rfl

/-! ## 2. The concrete place family and the collapse scalars -/

/-- The prime label `5`. -/
def finiteAlignmentFive : PrimeGeFive where
  value := 5
  prime := Nat.prime_five
  ge_five := le_rfl

/-- The singleton selection at the concrete Gaussian place over `5`. -/
def finiteAlignmentSelection : Finset (NumberField.FinitePlace GaussianField) :=
  {concreteGaussianFivePlace}

theorem finiteAlignmentSelection_nonempty :
    finiteAlignmentSelection.Nonempty :=
  Finset.singleton_nonempty concreteGaussianFivePlace

/-- The DVR q-candidate of the concrete place. -/
def finiteAlignmentParameters :
    (place : finiteAlignmentSelection) →
      NumberFieldFinitePlace.FinitePlaceQCandidate place.val :=
  fun place =>
    Classical.choice
      (NumberFieldFinitePlace.finitePlaceQCandidate_nonempty place.val)

/-- The object-level signed q-log of the concrete family: the common value of
every scalar below. -/
def finiteAlignmentQLog : ℝ :=
  ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
    finiteAlignmentSelection finiteAlignmentParameters

/-- Uniform hull pinned to the signed q-log. -/
def finiteAlignmentHull : FiniteHull Unit where
  volume := fun _ => finiteAlignmentQLog
  hullVolume := finiteAlignmentQLog
  contains := fun _ => le_rfl

/-- The finite certificate with all scalars at the signed q-log. -/
def finiteAlignmentCertificate : StepXIFiniteCertificate Unit :=
  StepXIFiniteCertificate.ofAbsoluteDegreeNormalizedSignedLog
    finiteAlignmentHull finiteAlignmentSelection finiteAlignmentParameters
    finiteAlignmentSelection_nonempty finiteAlignmentQLog le_rfl le_rfl

/-- The canonical-collapse QCMP supply over the same place family. -/
def finiteAlignmentSupply : StepXIQCMP.QCMPComparisonSupply GaussianField :=
  StepXIQCMP.QCMPComparisonSupply.ofCanonicalCollapse
    finiteAlignmentSelection finiteAlignmentParameters
    finiteAlignmentSelection_nonempty

@[simp] theorem finiteAlignmentCertificate_qSigned :
    finiteAlignmentCertificate.qSigned = finiteAlignmentQLog := rfl

@[simp] theorem finiteAlignmentSupply_thetaSigned :
    finiteAlignmentSupply.thetaSigned = finiteAlignmentQLog := rfl

/-! ## 3. The two alignment sockets, materialized -/

/-- First socket `hq_align` at the collapse point: definitional `le_rfl`. -/
theorem finiteAlignment_socket_q :
    finiteAlignmentCertificate.qSigned ≤
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        finiteAlignmentSupply.selectedLowerPlaces finiteAlignmentSupply.parameters :=
  le_rfl

/-- Second socket `hth` at the collapse point: definitional `le_rfl`. -/
theorem finiteAlignment_socket_theta :
    finiteAlignmentSupply.thetaSigned ≤ finiteAlignmentCertificate.thetaSigned :=
  le_rfl

/-! ## 4. Complete inhabitant of the IPL-wired link evidence -/

/-- The identity link on the test kernel.  The type of `LinkSpan.refl` is
fully pinned (`mid := Choice`), so no universe level is left open. -/
def finiteAlignmentLinkSpan :=
  Theorem311Source.PolyIsoTransport.LinkSpan.refl finiteAlignmentTestCore

/-- The canonical kernel-level Card-IPL supply on the identity link. -/
def finiteAlignmentIPLSupply :
    Theorem311Source.PolyIsoTransport.CardIPLTransportSupply
      finiteAlignmentLinkSpan :=
  Theorem311Source.PolyIsoTransport.trivialSupply finiteAlignmentLinkSpan

/-- The finite link evidence, with both sockets supplied by the collapse
theorems and the (SHE)/(APT) slots by the landed finite propositions. -/
def finiteAlignmentLinkEvidence :
    FiniteStepXILinkEvidence finiteAlignmentCertificate :=
  linkEvidenceOfQCMPWithIPL finiteAlignmentSupply finiteAlignmentCertificate
    finiteAlignment_socket_q finiteAlignment_socket_theta
    finiteAlignmentLinkSpan finiteAlignmentIPLSupply
    (ConcreteFiniteStepXI.finiteSHEProposition finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteAPTProposition finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteSHEProposition_proved finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteAPTProposition_proved finiteAlignmentFive 0)

/-- The contract assembled from the finite instance. -/
def finiteAlignmentContract : StepXIContract :=
  finiteAlignmentCertificate.toContract finiteAlignmentLinkEvidence

/-- Headline: the Cor 3.12 ordered conclusion on the finite test carrier,
through the existing consumer `cor312Conclusion_of_QCMPWithIPL`. -/
theorem finiteAlignmentConclusion :
    Cor312Conclusion finiteAlignmentContract :=
  cor312Conclusion_of_QCMPWithIPL finiteAlignmentSupply finiteAlignmentCertificate
    finiteAlignment_socket_q finiteAlignment_socket_theta
    finiteAlignmentLinkSpan finiteAlignmentIPLSupply
    (ConcreteFiniteStepXI.finiteSHEProposition finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteAPTProposition finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteSHEProposition_proved finiteAlignmentFive 0)
    (ConcreteFiniteStepXI.finiteAPTProposition_proved finiteAlignmentFive 0)

end StepXILinkWiring

end

namespace Audit

/-- The finite alignment-socket instance on the concrete Gaussian carrier. -/
def finiteAlignmentSocketInstance : Obligation :=
  { id := "IUT-III.finite-alignment-socket-instance"
    source :=
      "IUT III, Corollary 3.12, proof, Step (xi) (link data list (xi-b)); " ++
        "Remark 3.11.1, (iii) (IPL), (iv) (APT / HIS)"
    status := VerificationStatus.testCarrier
    note :=
      "Finite test-carrier inhabitant of `linkEvidenceOfQCMPWithIPL` on the " ++
        "concrete Gaussian field at its concrete place over 5 " ++
        "(`concreteGaussianFivePlace`).  Every scalar is definitionally the " ++
        "same object-level signed q-log of the same place family, so both " ++
        "alignment sockets (`hq_align`, `hth`) are `le_rfl` at the canonical-" ++
        "collapse point of `QCMPComparisonSupply.ofCanonicalCollapse`; the " ++
        "(IPL) slot is the landed exchange shape via `trivialSupply`; the " ++
        "(SHE)/(APT) slots are the landed finite propositions of " ++
        "`ConcreteFiniteRouteColumns.lean`.  Boundary: finite test carrier " ++
        "only -- no Theta-link or pilot data, degenerate collapse point " ++
        "q = target = theta; this is not a source instantiation of the " ++
        "supply, and the non-degenerate source-level alignment identification " ++
        "remains open."
    dependsOn :=
      [ "IUT-III.finite-certificate-link-evidence-wiring",
        "IUT-III.finite-certificate-to-contract",
        "IUT-III.card-qcmp-comparison-canonical-collapse",
        "IUT-III.card-ipl-poly-iso-transport-laws",
        "IUT-III.card-ipl-transport-canonical-discharge",
        "IUT-III.concrete-finite-stepXI-route",
        "IUT-I.concrete-initial-theta-finite-place-boundary",
        "IUT-III.holomorphic-hull-determinant-log-volume",
        "Foundations.NumberField.local-q-parameter-valuation",
        "Foundations.Arithmetic.prime-label-ge-five" ] }

end Audit

end LeanFormal.IUT
