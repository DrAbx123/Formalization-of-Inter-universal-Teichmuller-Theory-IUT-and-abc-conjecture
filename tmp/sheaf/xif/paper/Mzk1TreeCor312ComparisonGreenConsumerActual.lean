import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 comparison green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonGreenConsumerActual

open LeanFormal.IUT

theorem treeCor312ComparisonGreen_bundle (contract : StepXIContract) :
    Cor312Conclusion contract ∧
      (0 < -contract.qSigned) ∧
      Cor312Conclusion ({ route := Cor312Route.sarkisyanErdosKac, contract := contract } : Cor312RouteCertificate).contract :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_contract_cor312 contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_q_positive contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 Cor312Route.sarkisyanErdosKac contract⟩

def treeCor312ComparisonGreenRows : List (String × String × String) :=
  [ ("contract + q-positive + route bundle", "PROVED", "treeCor312ComparisonGreen_bundle") ]

theorem treeCor312ComparisonGreenRows_length : treeCor312ComparisonGreenRows.length = 1 := rfl

#check treeCor312ComparisonGreen_bundle
#check treeCor312ComparisonGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonGreenConsumerActual
end