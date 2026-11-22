import tmp.sheaf.xif.paper.Mzk1TreeStepXIBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree StepXI green bundle consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIGreenBundleActual

open LeanFormal.IUT

theorem treeStepXIGreen_bundle (contract : StepXIContract) (route : Cor312Route) :
    Cor312Conclusion contract ∧
      Cor312Conclusion ({ route := route, contract := contract } : Cor312RouteCertificate).contract ∧
      ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIBundleActual.stepXI_contract_bundle contract route

theorem treeStepXIGreen_allRoutes (contract : StepXIContract) :
    Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.arithmeticTeichmuller, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.sarkisyanErdosKac, contract := contract } : Cor312RouteCertificate).contract :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_all_routes_cor312 contract

def treeStepXIGreenRows : List (String × String × String) :=
  [ ("contract bundle", "PROVED", "treeStepXIGreen_bundle"),
    ("all routes", "PROVED", "treeStepXIGreen_allRoutes") ]

theorem treeStepXIGreenRows_length : treeStepXIGreenRows.length = 2 := rfl

#check treeStepXIGreen_bundle
#check treeStepXIGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIGreenBundleActual
end