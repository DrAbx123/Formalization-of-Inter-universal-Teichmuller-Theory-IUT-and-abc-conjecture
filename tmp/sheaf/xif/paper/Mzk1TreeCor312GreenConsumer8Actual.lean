import tmp.sheaf.xif.paper.Mzk1TreeCor312GreenFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 green consumer 8; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenConsumer8Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual

theorem treeCor312GreenConsumer8_q (contract : StepXIContract) :
    0 < -contract.qSigned :=
  tree_q_positive contract

def treeCor312GreenConsumer8Rows : List (String × String × String) :=
  [ ("q-positive", "PROVED", "treeCor312GreenConsumer8_q") ]

theorem treeCor312GreenConsumer8Rows_length : treeCor312GreenConsumer8Rows.length = 1 := rfl

#check treeCor312GreenConsumer8_q
#check treeCor312GreenConsumer8Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenConsumer8Actual
end