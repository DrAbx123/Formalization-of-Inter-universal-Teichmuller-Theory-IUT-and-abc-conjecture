import tmp.sheaf.xif.paper.Mzk1TreeIQHullFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree IQ hull green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullGreenConsumerActual

open LeanFormal.IUT

universe u

theorem treeIQHullGreen_bundle {X : Type u} (W : IQHullLogVolumeInterface X)
    {lowerBound : ENNReal} (h : lowerBound ≤ W.logVolume W.imageSet) :
    W.imageSet ⊆ W.hull ∧ lowerBound ≤ W.logVolume W.hull ∧ W.logVolume W.hull < ⊤ :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullFactsActual.tree_iqHull_bundle W h

theorem treeIQHullGreen_finite {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.logVolume W.hull < ⊤ :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullFactsActual.tree_iqHull_finite W

def treeIQHullGreenRows : List (String × String × String) :=
  [ ("hull bundle", "PROVED", "treeIQHullGreen_bundle"),
    ("hull finite", "PROVED", "treeIQHullGreen_finite") ]

theorem treeIQHullGreenRows_length : treeIQHullGreenRows.length = 2 := rfl

#check treeIQHullGreen_bundle
#check treeIQHullGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullGreenConsumerActual
end