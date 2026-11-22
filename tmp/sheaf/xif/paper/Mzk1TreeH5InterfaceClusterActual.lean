import tmp.sheaf.xif.paper.Mzk1TreeHullInterfaceFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree H5 interface cluster; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeH5InterfaceClusterActual

open LeanFormal.IUT

universe u

theorem treeH5InterfaceCluster_bundle {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ ∧ HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual.treeHullFacts_bundle W

def treeH5InterfaceClusterRows : List (String × String × String) :=
  [ ("H5 interface bundle", "PROVED", "treeH5InterfaceCluster_bundle") ]

theorem treeH5InterfaceClusterRows_length : treeH5InterfaceClusterRows.length = 1 := rfl

#check treeH5InterfaceCluster_bundle
#check treeH5InterfaceClusterRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeH5InterfaceClusterActual
end