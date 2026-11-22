import tmp.sheaf.xif.paper.S3128Cor312StepXIAssemblyActual
import tmp.sheaf.xif.paper.S3127Cor312StepXIStageAssemblyActual

noncomputable section
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.S3128Cor312StepXIAssemblyActual
open LeanFormal.IUT.XiFPaper.S3127Cor312StepXIStageAssemblyActual

namespace LeanFormal.IUT.XiFPaper.S3128Cor312StepXICombinedConsumerActual

/-- Combined status row: the concrete finite Step-XI assembly is a test-carrier
unit; the audit stage assembly contributes pending/pending/pending/proved/interface. -/
def cor312StepXICombinedStatuses : List VerificationStatus :=
  [ VerificationStatus.testCarrier ] ++ cor312StepXIStageAssembly.map Obligation.status

@[simp] theorem cor312StepXICombinedStatuses_length :
    cor312StepXICombinedStatuses.length = 6 := rfl

theorem cor312StepXICombinedStatuses_eq :
    cor312StepXICombinedStatuses =
      [ VerificationStatus.testCarrier,
        VerificationStatus.pending,
        VerificationStatus.pending,
        VerificationStatus.pending,
        VerificationStatus.proved,
        VerificationStatus.interface ] := rfl

theorem cor312StepXICombinedStatuses_has_concrete :
    VerificationStatus.testCarrier ∈ cor312StepXICombinedStatuses := by
  simp [cor312StepXICombinedStatuses]

/-- Link the concrete finite assembly (which carries a Cor312Conclusion) to the
audit rows without promoting the finite model to a source-faithful actual. -/
def cor312StepXICombinedObligation : Obligation :=
  { id := "IUT-III.Cor312.StepXI.combined"
    source := "IUT III, Corollary 3.12 proof, Step (xi): concrete finite route + audit assembly"
    status := VerificationStatus.testCarrier
    note := "Consumer link: concrete finite Cor312StepXIConcreteAssembly supplies a Cor312Conclusion on an explicit finite route; audit stage rows keep pending/interface separate. No source-faithful or unconditional claim."
    dependsOn :=
      [ "IUT-III.Cor312.StepXI.concrete-finite-assembly",
        "IUT-III.Cor312.StepXI.assembly",
        "IUT-III.IPL", "IUT-III.SHE", "IUT-III.APT" ] }

#check cor312StepXICombinedStatuses_eq
#check cor312StepXICombinedObligation

end LeanFormal.IUT.XiFPaper.S3128Cor312StepXICombinedConsumerActual
end
