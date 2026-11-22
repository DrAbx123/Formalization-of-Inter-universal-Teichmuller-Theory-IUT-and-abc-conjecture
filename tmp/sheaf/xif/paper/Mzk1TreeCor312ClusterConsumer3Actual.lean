import tmp.sheaf.xif.paper.Mzk1TreeCor312ClusterRollupActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 cluster consumer 3; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterConsumer3Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterRollupActual

theorem treeCor312ClusterConsumer3_bundle (contract : StepXIContract) :
    Cor312Conclusion contract :=
  (treeCor312ClusterRollup_bundle contract).1

def treeCor312ClusterConsumer3Rows : List (String × String × String) :=
  [ ("Cor312", "PROVED", "treeCor312ClusterConsumer3_bundle") ]

theorem treeCor312ClusterConsumer3Rows_length : treeCor312ClusterConsumer3Rows.length = 1 := rfl

#check treeCor312ClusterConsumer3_bundle
#check treeCor312ClusterConsumer3Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterConsumer3Actual
end