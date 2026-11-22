import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonGreenAllActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 cluster rollup; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterRollupActual

open LeanFormal.IUT

theorem treeCor312ClusterRollup_bundle (contract : StepXIContract) :
    Cor312Conclusion contract ∧ (0 < -contract.qSigned) :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonGreenAllActual.treeCor312ComparisonGreenAll_bundle contract

def treeCor312ClusterRollupRows : List (String × String × String) :=
  [ ("contract + q", "PROVED", "treeCor312ClusterRollup_bundle") ]

theorem treeCor312ClusterRollupRows_length : treeCor312ClusterRollupRows.length = 1 := rfl

#check treeCor312ClusterRollup_bundle
#check treeCor312ClusterRollupRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterRollupActual
end