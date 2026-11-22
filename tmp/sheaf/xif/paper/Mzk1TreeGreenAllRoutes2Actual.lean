import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312RouteAuditActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree all-routes green bundle 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeGreenAllRoutes2Actual

open LeanFormal.IUT

theorem treeGreenAllRoutes2_bundle (contract : StepXIContract) :
    Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.arithmeticTeichmuller, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.sarkisyanErdosKac, contract := contract } : Cor312RouteCertificate).contract :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_all_routes_cor312 contract

theorem treeGreenAllRoutes2_enum (r : Cor312Route) :
    r = Cor312Route.mochizuki3115 ∨ r = Cor312Route.arithmeticTeichmuller ∨
      r = Cor312Route.sarkisyanErdosKac :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312RouteAuditActual.cor312Route_enum r

def treeGreenAllRoutes2Rows : List (String × String × String) :=
  [ ("all routes", "PROVED", "treeGreenAllRoutes2_bundle"),
    ("route enum", "PROVED", "treeGreenAllRoutes2_enum") ]

theorem treeGreenAllRoutes2Rows_length : treeGreenAllRoutes2Rows.length = 2 := rfl

#check treeGreenAllRoutes2_bundle
#check treeGreenAllRoutes2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeGreenAllRoutes2Actual
end