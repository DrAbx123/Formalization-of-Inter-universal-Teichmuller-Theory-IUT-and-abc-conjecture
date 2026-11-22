import tmp.sheaf.xif.paper.Mzk1TreeCor312GreenFactsActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 green facts consumer 3; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsConsumer3Actual

open LeanFormal.IUT

theorem treeCor312GreenFactsConsumer3_bundle (contract : StepXIContract) :
    Cor312Conclusion contract ∧ (0 < -contract.qSigned) ∧
      Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).contract :=
  ⟨(LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsActual.treeCor312Green_bundle contract Cor312Route.mochizuki3115).1,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_q_positive contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 Cor312Route.mochizuki3115 contract⟩

def treeCor312GreenFactsConsumer3Rows : List (String × String × String) :=
  [ ("Cor312 + q + route", "PROVED", "treeCor312GreenFactsConsumer3_bundle") ]

theorem treeCor312GreenFactsConsumer3Rows_length : treeCor312GreenFactsConsumer3Rows.length = 1 := rfl

#check treeCor312GreenFactsConsumer3_bundle
#check treeCor312GreenFactsConsumer3Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsConsumer3Actual
end