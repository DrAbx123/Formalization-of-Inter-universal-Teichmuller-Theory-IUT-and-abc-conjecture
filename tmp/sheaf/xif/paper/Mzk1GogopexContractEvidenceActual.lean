/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1GogopexIplSheObjectsActual
import tmp.sheaf.xif.paper.Mzk1GogopexContainmentBridgeActual

/-! # A519: real contract evidence (IPL/SHE/APT objects into the StepXI contract) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexContractEvidence

open LeanFormal.IUT
open Iut RealLineCopy
open LeanFormal.IUT.Objects.GogopexIplShe
open LeanFormal.IUT.Objects.GogopexContainment

universe u

variable {source target : Copy} {index : Type u}

/-- The StepXI contract built from a Gogopex Stage-1 comparison with **actual** evidence:
an IPL object over the transported family (input prime-strip link), an SHE object
(structured simultaneous holomorphic expression), and the APT transport mechanism carried
by the IPL object. -/
def contractWithEvidence (C : Stage1.Stage1Comparison)
    {family : TransportedRegionFamily source target index}
    (I : IPLObject family) (S : SHEObject family) : StepXIContract :=
  stepXIContractOfComparison C
    (Nonempty (IPLObject family))
    (QualitativeData.HasStructuredSHE family)
    (Nonempty QualitativeData.TransportMechanismId)
    ⟨I⟩ S.hasStructuredSHE ⟨I.mechanism⟩

/-- The evidence-built contract satisfies the Corollary 3.12 conclusion (no True/trivial
placeholder: the IPL/SHE/APT fields are witnessed by actual objects). -/
theorem cor312Conclusion_of_evidence (C : Stage1.Stage1Comparison)
    {family : TransportedRegionFamily source target index}
    (I : IPLObject family) (S : SHEObject family) :
    Cor312Conclusion (contractWithEvidence C I S) :=
  cor312_of_constructed_stepXI _

/-- The contract's qSigned is exactly `-q.value` (the q-pilot signed log-volume). -/
theorem contractWithEvidence_qSigned (C : Stage1.Stage1Comparison)
    {family : TransportedRegionFamily source target index}
    (I : IPLObject family) (S : SHEObject family) :
    (contractWithEvidence C I S).qSigned = -C.q.value := rfl

/-- The contract's thetaSigned is exactly `-theta.value` (the Theta-pilot signed log-volume). -/
theorem contractWithEvidence_thetaSigned (C : Stage1.Stage1Comparison)
    {family : TransportedRegionFamily source target index}
    (I : IPLObject family) (S : SHEObject family) :
    (contractWithEvidence C I S).thetaSigned = -C.theta.value := rfl

/-- The IPL field of the evidence-built contract is the nonemptiness of the actual IPL object. -/
theorem contractWithEvidence_ipl (C : Stage1.Stage1Comparison)
    {family : TransportedRegionFamily source target index}
    (I : IPLObject family) (S : SHEObject family) :
    (contractWithEvidence C I S).ipl = Nonempty (IPLObject family) := rfl

end LeanFormal.IUT.Objects.GogopexContractEvidence
