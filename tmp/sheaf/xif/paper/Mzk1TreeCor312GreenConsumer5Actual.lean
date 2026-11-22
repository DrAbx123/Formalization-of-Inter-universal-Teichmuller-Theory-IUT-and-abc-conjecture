import tmp.sheaf.xif.paper.Mzk1TreeCor312GreenFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 green consumer 5; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenConsumer5Actual

open LeanFormal.IUT

theorem treeCor312GreenConsumer5_bundle (contract : StepXIContract) (r : Cor312Route) :
    Cor312Conclusion contract ∧
      (r = Cor312Route.mochizuki3115 ∨ r = Cor312Route.arithmeticTeichmuller ∨
        r = Cor312Route.sarkisyanErdosKac) :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsActual.treeCor312Green_bundle contract r

def treeCor312GreenConsumer5Rows : List (String × String × String) :=
  [ ("contract + enum", "PROVED", "treeCor312GreenConsumer5_bundle") ]

theorem treeCor312GreenConsumer5Rows_length : treeCor312GreenConsumer5Rows.length = 1 := rfl

#check treeCor312GreenConsumer5_bundle
#check treeCor312GreenConsumer5Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenConsumer5Actual
end