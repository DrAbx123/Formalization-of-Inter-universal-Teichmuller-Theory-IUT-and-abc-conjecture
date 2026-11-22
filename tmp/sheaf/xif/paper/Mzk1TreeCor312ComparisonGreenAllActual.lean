import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 comparison green all; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonGreenAllActual

open LeanFormal.IUT

theorem treeCor312ComparisonGreenAll_bundle (contract : StepXIContract) :
    Cor312Conclusion contract ∧ (0 < -contract.qSigned) :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_contract_cor312 contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_q_positive contract⟩

def treeCor312ComparisonGreenAllRows : List (String × String × String) :=
  [ ("contract + q-positive", "PROVED", "treeCor312ComparisonGreenAll_bundle") ]

theorem treeCor312ComparisonGreenAllRows_length : treeCor312ComparisonGreenAllRows.length = 1 := rfl

#check treeCor312ComparisonGreenAll_bundle
#check treeCor312ComparisonGreenAllRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonGreenAllActual
end