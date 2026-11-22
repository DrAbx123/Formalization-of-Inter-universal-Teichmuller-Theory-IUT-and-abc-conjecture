import tmp.sheaf.xif.paper.Mzk1TreeStepXIBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # iutiv-abc StepXI interface consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIInterfaceConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit

theorem stepXIInterfaceConsumer_bundle (contract : StepXIContract) (route : Cor312Route) :
    Cor312Conclusion contract ∧
      Cor312Conclusion ({ route := route, contract := contract } : Cor312RouteCertificate).contract ∧
      ipl.id = "IUT-III.IPL" :=
  have h := LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIBundleActual.stepXI_contract_bundle contract route
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem stepXIInterfaceConsumer_qpositive (contract : StepXIContract) : 0 < -contract.qSigned :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_q_positive contract

def stepXIInterfaceConsumerRows : List (String × String × String) :=
  [ ("StepXI contract consumer", "PROVED", "stepXIInterfaceConsumer_bundle"),
    ("q-positive", "PROVED", "stepXIInterfaceConsumer_qpositive") ]

theorem stepXIInterfaceConsumerRows_length : stepXIInterfaceConsumerRows.length = 2 := rfl

#check stepXIInterfaceConsumer_bundle
#check stepXIInterfaceConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIInterfaceConsumerActual
end