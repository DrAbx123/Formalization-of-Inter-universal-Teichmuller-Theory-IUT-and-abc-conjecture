import tmp.sheaf.xif.paper.Mzk1TreeStepXIBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312RouteAuditActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree green all consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeGreenAllConsumerActual

open LeanFormal.IUT

theorem treeGreenAllConsumer_bundle (contract : StepXIContract) :
    Cor312Conclusion contract ∧
      (0 < -contract.qSigned) ∧
      Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.arithmeticTeichmuller, contract := contract } : Cor312RouteCertificate).contract :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIBundleActual.stepXI_contract_bundle contract Cor312Route.mochizuki3115 |>.1,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_q_positive contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 _ contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 _ contract⟩

def treeGreenAllConsumerRows : List (String × String × String) :=
  [ ("contract + q-positive + two routes", "PROVED", "treeGreenAllConsumer_bundle") ]

theorem treeGreenAllConsumerRows_length : treeGreenAllConsumerRows.length = 1 := rfl

#check treeGreenAllConsumer_bundle
#check treeGreenAllConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeGreenAllConsumerActual
end