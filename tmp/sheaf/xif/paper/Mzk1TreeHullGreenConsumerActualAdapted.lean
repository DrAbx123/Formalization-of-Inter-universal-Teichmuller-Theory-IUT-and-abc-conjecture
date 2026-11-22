import tmp.sheaf.xif.paper.Mzk1TreeHullBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeIQHullFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree hull green consumer bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeHullGreenConsumerActualAdapted

open LeanFormal.IUT

universe u

theorem treeHullGreen_bundle {X : Type u} (W : IQHullLogVolumeInterface X) :
    HullDeterminantLogVolumeFrozenSpec ∧ W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetTensorBundleActual.h5_frozenSpec,
    LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullFactsActual.tree_iqHull_image_subset W,
    LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullFactsActual.tree_iqHull_finite W⟩

def treeHullGreenRows : List (String × String × String) :=
  [ ("frozen det + hull bundle", "PROVED", "treeHullGreen_bundle") ]

theorem treeHullGreenRows_length : treeHullGreenRows.length = 1 := rfl

#check treeHullGreen_bundle
#check treeHullGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeHullGreenConsumerActualAdapted
end