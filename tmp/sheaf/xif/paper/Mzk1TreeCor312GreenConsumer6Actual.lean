import tmp.sheaf.xif.paper.Mzk1TreeCor312GreenFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 green consumer 6; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenConsumer6Actual

open LeanFormal.IUT

theorem treeCor312GreenConsumer6_contract (contract : StepXIContract) :
    Cor312Conclusion contract :=
  (LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsActual.treeCor312Green_bundle contract Cor312Route.mochizuki3115).1

def treeCor312GreenConsumer6Rows : List (String × String × String) :=
  [ ("Cor312", "PROVED", "treeCor312GreenConsumer6_contract") ]

theorem treeCor312GreenConsumer6Rows_length : treeCor312GreenConsumer6Rows.length = 1 := rfl

#check treeCor312GreenConsumer6_contract
#check treeCor312GreenConsumer6Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenConsumer6Actual
end