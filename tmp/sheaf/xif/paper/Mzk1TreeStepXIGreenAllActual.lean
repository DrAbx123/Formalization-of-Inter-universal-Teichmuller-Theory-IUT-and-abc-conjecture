import tmp.sheaf.xif.paper.Mzk1TreeStepXIBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree StepXI green all bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIGreenAllActual

open LeanFormal.IUT

theorem treeStepXIGreenAll_bundle (contract : StepXIContract) :
    Cor312Conclusion contract ∧ (0 < -contract.qSigned) ∧
      Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).contract :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIBundleActual.stepXI_contract_bundle contract Cor312Route.mochizuki3115 |>.1,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_q_positive contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 _ contract⟩

def treeStepXIGreenAllRows : List (String × String × String) :=
  [ ("Cor312 + q-positive + route bundle", "PROVED", "treeStepXIGreenAll_bundle") ]

theorem treeStepXIGreenAllRows_length : treeStepXIGreenAllRows.length = 1 := rfl

#check treeStepXIGreenAll_bundle
#check treeStepXIGreenAllRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIGreenAllActual
end