import tmp.sheaf.xif.paper.S3127Cor312StepXIAssemblyActual
import LeanFormal.IUT.IUTIII.Corollary312.Obligations

noncomputable section
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.S3127Cor312StepXIAssemblyActual

namespace LeanFormal.IUT.XiFPaper.S3127Cor312StepXIStageAssemblyActual

/-- Next layer: Step-XI entry points (pending) followed by the proved/interface
assembly consumer. -/
def cor312StepXIStageAssembly : List Obligation :=
  [ ipl, she, apt ] ++ cor312StepXIAssemblyObligations

@[simp] theorem cor312StepXIStageAssembly_length :
    cor312StepXIStageAssembly.length = 5 := rfl

theorem cor312StepXIStageAssembly_statuses :
    cor312StepXIStageAssembly.map Obligation.status =
      [ VerificationStatus.pending,
        VerificationStatus.pending,
        VerificationStatus.pending,
        VerificationStatus.proved,
        VerificationStatus.interface ] := rfl

theorem cor312StepXIStageAssembly_append :
    cor312StepXIStageAssembly =
      [ipl, she, apt] ++ cor312StepXIAssemblyObligations := rfl

theorem cor312StepXIStageAssembly_contains_assembly :
    ∀ o ∈ cor312StepXIAssemblyObligations, o ∈ cor312StepXIStageAssembly := by
  intro o ho
  simp [cor312StepXIStageAssembly, ho]

/-- The assembly component ids are exactly the ids listed in its dependency field. -/
theorem cor312StepXIAssembly_dependsOn_covers :
    ∀ id ∈ cor312StepXIAssembly.dependsOn,
      ∃ o ∈ cor312StepXIAssemblyObligations, o.id = id := by
  intro id hid
  simp [cor312StepXIAssembly, cor312StepXIAssemblyObligations] at hid
  rcases hid with rfl | rfl
  · exact ⟨finiteThetaPacketBridge, by simp [cor312StepXIAssemblyObligations], rfl⟩
  · exact ⟨sourceProcessionStepXIXifInclusionResidual,
      by simp [cor312StepXIAssemblyObligations], rfl⟩

#check cor312StepXIStageAssembly
#check cor312StepXIAssembly_dependsOn_covers

end LeanFormal.IUT.XiFPaper.S3127Cor312StepXIStageAssemblyActual
end
