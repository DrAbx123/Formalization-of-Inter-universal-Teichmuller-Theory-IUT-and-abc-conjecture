import tmp.sheaf.xif.paper.Mzk1TreeStepXIBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree StepXI green bundle consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIGreenBundleConsumerActual

open LeanFormal.IUT

theorem treeStepXIGreenBundleConsumer_bundle (contract : StepXIContract) :
    Cor312Conclusion contract ∧
      Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).contract :=
  ⟨(LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIBundleActual.stepXI_contract_bundle contract Cor312Route.mochizuki3115).1,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 _ contract⟩

def treeStepXIGreenBundleConsumerRows : List (String × String × String) :=
  [ ("tree StepXI green bundle", "PROVED", "treeStepXIGreenBundleConsumer_bundle") ]

theorem treeStepXIGreenBundleConsumerRows_length : treeStepXIGreenBundleConsumerRows.length = 1 := rfl

#check treeStepXIGreenBundleConsumer_bundle
#check treeStepXIGreenBundleConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIGreenBundleConsumerActual
end