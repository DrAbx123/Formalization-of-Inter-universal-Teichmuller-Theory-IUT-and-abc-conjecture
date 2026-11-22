import tmp.sheaf.xif.paper.Mzk1TreeIQHullFactsActual
import tmp.sheaf.xif.paper.Mzk1TreeHullInterfaceFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree IQ hull green all; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullGreenAllActual

open LeanFormal.IUT

universe u

theorem treeIQHullGreenAll_bundle {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ ∧ HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual.treeHullFacts_bundle W

theorem treeIQHullGreenAll_lower {X : Type u} (W : IQHullLogVolumeInterface X)
    {lowerBound : ENNReal} (h : lowerBound ≤ W.logVolume W.imageSet) :
    lowerBound ≤ W.logVolume W.hull :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullFactsActual.tree_iqHull_lower_bound W h

def treeIQHullGreenAllRows : List (String × String × String) :=
  [ ("hull bundle", "PROVED", "treeIQHullGreenAll_bundle"),
    ("lower bound", "PROVED", "treeIQHullGreenAll_lower") ]

theorem treeIQHullGreenAllRows_length : treeIQHullGreenAllRows.length = 2 := rfl

#check treeIQHullGreenAll_bundle
#check treeIQHullGreenAllRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullGreenAllActual
end