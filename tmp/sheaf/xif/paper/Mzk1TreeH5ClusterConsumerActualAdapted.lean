import tmp.sheaf.xif.paper.Mzk1TreeH5GreenAllActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree H5 cluster consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeH5ClusterConsumerActualAdapted

open LeanFormal.IUT

theorem treeH5ClusterConsumer_bundle : HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeH5GreenAllActual.treeH5GreenAll_bundle |>.1

def treeH5ClusterConsumerRows : List (String × String × String) :=
  [ ("frozen det spec", "PROVED", "treeH5ClusterConsumer_bundle") ]

theorem treeH5ClusterConsumerRows_length : treeH5ClusterConsumerRows.length = 1 := rfl

#check treeH5ClusterConsumer_bundle
#check treeH5ClusterConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeH5ClusterConsumerActualAdapted
end