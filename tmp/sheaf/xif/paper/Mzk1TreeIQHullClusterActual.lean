import tmp.sheaf.xif.paper.Mzk1TreeIQHullFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree IQ hull cluster; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullClusterActual

open LeanFormal.IUT

universe u

theorem treeIQHullCluster_bundle {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ :=
  ⟨W.imageSet_subset_hull, W.hull_logVolume_lt_top⟩

def treeIQHullClusterRows : List (String × String × String) :=
  [ ("image subset + finite", "PROVED", "treeIQHullCluster_bundle") ]

theorem treeIQHullClusterRows_length : treeIQHullClusterRows.length = 1 := rfl

#check treeIQHullCluster_bundle
#check treeIQHullClusterRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullClusterActual
end