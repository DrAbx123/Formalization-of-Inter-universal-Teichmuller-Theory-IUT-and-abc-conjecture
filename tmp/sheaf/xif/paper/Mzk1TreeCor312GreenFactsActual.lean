import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312RouteAuditActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 green facts bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsActual

open LeanFormal.IUT

theorem treeCor312Green_allRoutes (contract : StepXIContract) :
    Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.arithmeticTeichmuller, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.sarkisyanErdosKac, contract := contract } : Cor312RouteCertificate).contract :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_all_routes_cor312 contract

theorem treeCor312Green_routeEnum (r : Cor312Route) :
    r = Cor312Route.mochizuki3115 ∨ r = Cor312Route.arithmeticTeichmuller ∨
      r = Cor312Route.sarkisyanErdosKac :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312RouteAuditActual.cor312Route_enum r

theorem treeCor312Green_bundle (contract : StepXIContract) (r : Cor312Route) :
    Cor312Conclusion contract ∧ (r = Cor312Route.mochizuki3115 ∨ r = Cor312Route.arithmeticTeichmuller ∨
      r = Cor312Route.sarkisyanErdosKac) :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_contract_cor312 contract,
    treeCor312Green_routeEnum r⟩

def treeCor312GreenRows : List (String × String × String) :=
  [ ("all-routes certificates", "PROVED", "treeCor312Green_allRoutes"),
    ("route enumeration", "PROVED", "treeCor312Green_routeEnum"),
    ("bundle", "PROVED", "treeCor312Green_bundle") ]

theorem treeCor312GreenRows_length : treeCor312GreenRows.length = 3 := rfl

#check treeCor312Green_bundle
#check treeCor312GreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsActual
end