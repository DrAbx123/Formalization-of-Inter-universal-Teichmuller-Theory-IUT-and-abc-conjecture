import tmp.sheaf.xif.paper.Mzk1TreeH5DetTensorBundleActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree H5 det consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetConsumerActual

open LeanFormal.IUT

theorem treeH5DetConsumer_bundle : HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetTensorBundleActual.h5_frozenSpec

def treeH5DetConsumerRows : List (String × String × String) :=
  [ ("frozen spec", "PROVED", "treeH5DetConsumer_bundle") ]

theorem treeH5DetConsumerRows_length : treeH5DetConsumerRows.length = 1 := rfl

#check treeH5DetConsumer_bundle
#check treeH5DetConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetConsumerActual
end