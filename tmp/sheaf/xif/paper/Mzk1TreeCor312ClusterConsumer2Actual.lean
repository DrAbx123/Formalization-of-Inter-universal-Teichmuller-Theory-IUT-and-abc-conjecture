import tmp.sheaf.xif.paper.Mzk1TreeCor312GreenFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 cluster consumer 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterConsumer2Actual

open LeanFormal.IUT

theorem treeCor312ClusterConsumer2_allRoutes (contract : StepXIContract) :
    Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).contract :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 Cor312Route.mochizuki3115 contract

theorem treeCor312ClusterConsumer2_enum (r : Cor312Route) :
    r = Cor312Route.mochizuki3115 ∨ r = Cor312Route.arithmeticTeichmuller ∨
      r = Cor312Route.sarkisyanErdosKac :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312RouteAuditActual.cor312Route_enum r

def treeCor312ClusterConsumer2Rows : List (String × String × String) :=
  [ ("route certificate", "PROVED", "treeCor312ClusterConsumer2_allRoutes"),
    ("route enum", "PROVED", "treeCor312ClusterConsumer2_enum") ]

theorem treeCor312ClusterConsumer2Rows_length : treeCor312ClusterConsumer2Rows.length = 2 := rfl

#check treeCor312ClusterConsumer2_allRoutes
#check treeCor312ClusterConsumer2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterConsumer2Actual
end