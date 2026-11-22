import tmp.sheaf.xif.paper.Mzk1TreeCor312GreenFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 green facts consumer 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsConsumer2Actual

open LeanFormal.IUT

theorem treeCor312GreenFactsConsumer2_bundle (contract : StepXIContract) (r : Cor312Route) :
    Cor312Conclusion contract ∧
      (r = Cor312Route.mochizuki3115 ∨ r = Cor312Route.arithmeticTeichmuller ∨
        r = Cor312Route.sarkisyanErdosKac) :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsActual.treeCor312Green_bundle contract r

def treeCor312GreenFactsConsumer2Rows : List (String × String × String) :=
  [ ("contract + route enum", "PROVED", "treeCor312GreenFactsConsumer2_bundle") ]

theorem treeCor312GreenFactsConsumer2Rows_length : treeCor312GreenFactsConsumer2Rows.length = 1 := rfl

#check treeCor312GreenFactsConsumer2_bundle
#check treeCor312GreenFactsConsumer2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsConsumer2Actual
end