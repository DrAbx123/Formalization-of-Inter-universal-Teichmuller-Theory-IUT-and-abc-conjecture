import tmp.sheaf.xif.paper.Mzk1TreeCor312ClusterRollupActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 cluster consumer 4; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterConsumer4Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual
open LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterRollupActual

theorem treeCor312ClusterConsumer4_route (contract : StepXIContract) :
    Cor312Conclusion ({ route := Cor312Route.sarkisyanErdosKac, contract := contract } : Cor312RouteCertificate).contract :=
  tree_route_cor312 Cor312Route.sarkisyanErdosKac contract

def treeCor312ClusterConsumer4Rows : List (String × String × String) :=
  [ ("route certificate", "PROVED", "treeCor312ClusterConsumer4_route") ]

theorem treeCor312ClusterConsumer4Rows_length : treeCor312ClusterConsumer4Rows.length = 1 := rfl

#check treeCor312ClusterConsumer4_route
#check treeCor312ClusterConsumer4Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterConsumer4Actual
end