import tmp.sheaf.xif.paper.Mzk1TreeH5DetTensorBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeDetFrozenActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree H5 frozen green all; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeH5GreenAllActual

open LeanFormal.IUT

theorem treeH5GreenAll_bundle :
    HullDeterminantLogVolumeFrozenSpec ∧ HullDeterminantLogVolumeFrozenSpec :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetTensorBundleActual.h5_frozenSpec,
    LeanFormal.IUT.XiFPaper.Mzk1TreeDetFrozenActual.tree_detFrozenSpec_holds⟩

def treeH5GreenAllRows : List (String × String × String) :=
  [ ("frozen det spec (two consumers)", "PROVED", "treeH5GreenAll_bundle") ]

theorem treeH5GreenAllRows_length : treeH5GreenAllRows.length = 1 := rfl

#check treeH5GreenAll_bundle
#check treeH5GreenAllRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeH5GreenAllActual
end