import tmp.sheaf.xif.paper.Mzk1TreeCor312GreenFactsActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 green facts consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsConsumerActual

open LeanFormal.IUT

theorem treeCor312GreenFactsConsumer_bundle (contract : StepXIContract) :
    Cor312Conclusion contract ∧
      (0 < -contract.qSigned) :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsActual.treeCor312Green_bundle contract Cor312Route.mochizuki3115 |>.1,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_q_positive contract⟩

def treeCor312GreenFactsConsumerRows : List (String × String × String) :=
  [ ("green facts bundle", "PROVED", "treeCor312GreenFactsConsumer_bundle") ]

theorem treeCor312GreenFactsConsumerRows_length : treeCor312GreenFactsConsumerRows.length = 1 := rfl

#check treeCor312GreenFactsConsumer_bundle
#check treeCor312GreenFactsConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsConsumerActual
end