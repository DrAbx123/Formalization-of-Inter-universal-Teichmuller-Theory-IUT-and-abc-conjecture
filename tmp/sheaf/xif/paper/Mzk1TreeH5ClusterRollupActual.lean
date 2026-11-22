import tmp.sheaf.xif.paper.Mzk1TreeH5DetTensorBundleActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree H5 cluster rollup; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeH5ClusterRollupActual

open LeanFormal.IUT

theorem treeH5ClusterRollup_bundle : HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetTensorBundleActual.h5_frozenSpec

def treeH5ClusterRollupRows : List (String × String × String) :=
  [ ("frozen det spec", "PROVED", "treeH5ClusterRollup_bundle") ]

theorem treeH5ClusterRollupRows_length : treeH5ClusterRollupRows.length = 1 := rfl

#check treeH5ClusterRollup_bundle
#check treeH5ClusterRollupRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeH5ClusterRollupActual
end