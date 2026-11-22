import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ThetaPacketBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceProcessionStepXIInclusionResidual
import LeanFormal.IUT.Audit.Status

noncomputable section
open LeanFormal.IUT.Audit

namespace LeanFormal.IUT.XiFPaper.S3127Cor312StepXIAssemblyActual

/-- Assembly of the two Step-XI actual units with the smallest dependency cone:
the finite theta-packet bridge (proved) and the (xi-d)-(xi-f) inclusion residual
(interface). This is a consumer, not a new proof. -/
def cor312StepXIAssemblyObligations : List Obligation :=
  [ finiteThetaPacketBridge, sourceProcessionStepXIXifInclusionResidual ]

@[simp] theorem cor312StepXIAssemblyObligations_length :
    cor312StepXIAssemblyObligations.length = 2 := rfl

theorem cor312StepXIAssemblyObligations_nonempty :
    cor312StepXIAssemblyObligations ≠ [] := by
  simp [cor312StepXIAssemblyObligations]

theorem cor312StepXIAssemblyObligations_has_proved :
    ∃ o ∈ cor312StepXIAssemblyObligations, o.status = VerificationStatus.proved := by
  refine ⟨finiteThetaPacketBridge, ?_, rfl⟩
  simp [cor312StepXIAssemblyObligations]

theorem cor312StepXIAssemblyObligations_statuses :
    cor312StepXIAssemblyObligations.map Obligation.status =
      [VerificationStatus.proved, VerificationStatus.interface] := rfl

/-- Aggregated audit obligation for the Cor 3.12 Step-XI assembly consumer. -/
def cor312StepXIAssembly : Obligation :=
  { id := "IUT-III.Cor312.StepXI.assembly"
    source := "IUT III, Corollary 3.12 proof, Steps (xi-d)-(xi-f) (III:10843-10898)"
    status := VerificationStatus.interface
    note := "Consumer assembly of the finite theta-packet bridge and the (xi-f) inclusion residual. Does not assert the source holomorphic-hull or the signed C_Theta >= -1 comparison; those remain the component statuses."
    dependsOn :=
      [ "IUT-III.StepXI.finite-theta-packet-bridge",
        "IUT-III.source-procession-stepXI-xif-inclusion" ] }

#check cor312StepXIAssemblyObligations
#check cor312StepXIAssembly

end LeanFormal.IUT.XiFPaper.S3127Cor312StepXIAssemblyActual
end
