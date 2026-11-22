import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import tmp.sheaf.xif.paper.Mzk1IUTIIILinkActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI contract green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIContractGreenConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual

theorem stepXIContractGreenConsumer_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧ Cor312Conclusion L.toContract ∧
      (0 < -S.toContract.qSigned) ∧ (0 < -L.toContract.qSigned) :=
  ⟨sourceData_cor312 S, cor312Conclusion_of_IUTIIToStepXILink L,
    sourceData_q_positive S, q_positive_of_IUTIIToStepXILink L⟩

def stepXIContractGreenConsumerRows : List (String × String × String) :=
  [ ("both contracts + q-positive", "PROVED", "stepXIContractGreenConsumer_bundle") ]

theorem stepXIContractGreenConsumerRows_length : stepXIContractGreenConsumerRows.length = 1 := rfl

#check stepXIContractGreenConsumer_bundle
#check stepXIContractGreenConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIContractGreenConsumerActual
end