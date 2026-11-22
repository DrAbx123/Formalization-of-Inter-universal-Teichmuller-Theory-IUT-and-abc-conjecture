import tmp.sheaf.xif.paper.Mzk1TreeH5DetTensorBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeHullInterfaceFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree H5 green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeH5GreenConsumerActual

open LeanFormal.IUT

universe u

theorem treeH5Green_bundle {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ ∧ HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual.treeHullFacts_bundle W

def treeH5GreenRows : List (String × String × String) :=
  [ ("frozen det + interface bundle", "PROVED", "treeH5Green_bundle") ]

theorem treeH5GreenRows_length : treeH5GreenRows.length = 1 := rfl

#check treeH5Green_bundle
#check treeH5GreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeH5GreenConsumerActual
end