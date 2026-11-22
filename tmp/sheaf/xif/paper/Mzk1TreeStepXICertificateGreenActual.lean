import tmp.sheaf.xif.paper.Mzk1TreeStepXIBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree StepXI certificate green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeStepXICertificateGreenActual

open LeanFormal.IUT

theorem treeStepXICertificateGreen_bundle (contract : StepXIContract) (route : Cor312Route) :
    Cor312Conclusion ({ route := route, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion contract :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 route contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIBundleActual.stepXI_contract_bundle contract route |>.1⟩

def treeStepXICertificateGreenRows : List (String × String × String) :=
  [ ("route certificate + contract", "PROVED", "treeStepXICertificateGreen_bundle") ]

theorem treeStepXICertificateGreenRows_length : treeStepXICertificateGreenRows.length = 1 := rfl

#check treeStepXICertificateGreen_bundle
#check treeStepXICertificateGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeStepXICertificateGreenActual
end