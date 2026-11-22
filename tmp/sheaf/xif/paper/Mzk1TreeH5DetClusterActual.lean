import tmp.sheaf.xif.paper.Mzk1TreeH5DetTensorBundleActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree H5 det cluster; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetClusterActual

open LeanFormal.IUT

theorem treeH5DetCluster_bundle : HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetTensorBundleActual.h5_frozenSpec

def treeH5DetClusterRows : List (String × String × String) :=
  [ ("frozen spec", "PROVED", "treeH5DetCluster_bundle") ]

theorem treeH5DetClusterRows_length : treeH5DetClusterRows.length = 1 := rfl

#check treeH5DetCluster_bundle
#check treeH5DetClusterRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetClusterActual
end