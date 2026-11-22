import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312RouteAuditActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 green consumer 4; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenConsumer4ActualAdapted

open LeanFormal.IUT

theorem treeCor312GreenConsumer4_bundle (contract : StepXIContract) :
    Cor312Conclusion contract ∧ (0 < -contract.qSigned) :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_contract_cor312 contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_q_positive contract⟩

theorem treeCor312GreenConsumer4_enum (r : Cor312Route) :
    r = Cor312Route.mochizuki3115 ∨ r = Cor312Route.arithmeticTeichmuller ∨
      r = Cor312Route.sarkisyanErdosKac :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312RouteAuditActual.cor312Route_enum r

def treeCor312GreenConsumer4Rows : List (String × String × String) :=
  [ ("contract + q", "PROVED", "treeCor312GreenConsumer4_bundle"),
    ("enum", "PROVED", "treeCor312GreenConsumer4_enum") ]

theorem treeCor312GreenConsumer4Rows_length : treeCor312GreenConsumer4Rows.length = 2 := rfl

#check treeCor312GreenConsumer4_bundle
#check treeCor312GreenConsumer4Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenConsumer4ActualAdapted
end