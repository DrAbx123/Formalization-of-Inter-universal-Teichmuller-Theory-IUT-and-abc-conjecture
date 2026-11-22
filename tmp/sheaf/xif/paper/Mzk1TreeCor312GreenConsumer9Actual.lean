import tmp.sheaf.xif.paper.Mzk1TreeCor312GreenFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 green consumer 9; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenConsumer9Actual

open LeanFormal.IUT

theorem treeCor312GreenConsumer9_contract (contract : StepXIContract) :
    Cor312Conclusion contract :=
  (LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsActual.treeCor312Green_bundle contract Cor312Route.mochizuki3115).1

def treeCor312GreenConsumer9Rows : List (String × String × String) :=
  [ ("Cor312", "PROVED", "treeCor312GreenConsumer9_contract") ]

theorem treeCor312GreenConsumer9Rows_length : treeCor312GreenConsumer9Rows.length = 1 := rfl

#check treeCor312GreenConsumer9_contract
#check treeCor312GreenConsumer9Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenConsumer9Actual
end