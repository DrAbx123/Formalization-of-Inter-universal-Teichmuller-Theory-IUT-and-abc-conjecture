import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312RouteAuditActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 green route consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenRouteActual

open LeanFormal.IUT

theorem treeCor312GreenRoute_bundle (contract : StepXIContract) (r : Cor312Route) :
    Cor312Conclusion contract ∧
      (0 < -contract.qSigned) ∧
      (r = Cor312Route.mochizuki3115 ∨ r = Cor312Route.arithmeticTeichmuller ∨
        r = Cor312Route.sarkisyanErdosKac) :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_contract_cor312 contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_q_positive contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312RouteAuditActual.cor312Route_enum r⟩

def treeCor312GreenRouteRows : List (String × String × String) :=
  [ ("contract + q-positive + route enum", "PROVED", "treeCor312GreenRoute_bundle") ]

theorem treeCor312GreenRouteRows_length : treeCor312GreenRouteRows.length = 1 := rfl

#check treeCor312GreenRoute_bundle
#check treeCor312GreenRouteRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenRouteActual
end