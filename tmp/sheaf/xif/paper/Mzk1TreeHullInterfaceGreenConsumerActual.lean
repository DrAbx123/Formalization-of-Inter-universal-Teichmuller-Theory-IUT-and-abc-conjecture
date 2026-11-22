import tmp.sheaf.xif.paper.Mzk1TreeHullInterfaceFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree hull interface green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceGreenConsumerActual

open LeanFormal.IUT

universe u

theorem treeHullInterfaceGreen_bundle {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ ∧ HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual.treeHullFacts_bundle W

theorem treeHullInterfaceGreen_frozen : HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual.treeHullFacts_frozen

def treeHullInterfaceGreenRows : List (String × String × String) :=
  [ ("interface + frozen bundle", "PROVED", "treeHullInterfaceGreen_bundle"),
    ("frozen spec", "PROVED", "treeHullInterfaceGreen_frozen") ]

theorem treeHullInterfaceGreenRows_length : treeHullInterfaceGreenRows.length = 2 := rfl

#check treeHullInterfaceGreen_bundle
#check treeHullInterfaceGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceGreenConsumerActual
end