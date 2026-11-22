import tmp.sheaf.xif.paper.Mzk1TreeCor312ClusterRollupActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 cluster consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterRollupActual

theorem treeCor312ClusterConsumer_bundle (contract : StepXIContract) :
    Cor312Conclusion contract :=
  (treeCor312ClusterRollup_bundle contract).1

theorem treeCor312ClusterConsumer_q (contract : StepXIContract) :
    0 < -contract.qSigned :=
  (treeCor312ClusterRollup_bundle contract).2

def treeCor312ClusterConsumerRows : List (String × String × String) :=
  [ ("Cor312", "PROVED", "treeCor312ClusterConsumer_bundle"),
    ("q-positive", "PROVED", "treeCor312ClusterConsumer_q") ]

theorem treeCor312ClusterConsumerRows_length : treeCor312ClusterConsumerRows.length = 2 := rfl

#check treeCor312ClusterConsumer_bundle
#check treeCor312ClusterConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ClusterConsumerActualAdapted
end