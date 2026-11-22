import tmp.sheaf.xif.paper.Mzk1TreeH5DetTensorBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeHullInterfaceFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree H5 interface green bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeH5InterfaceGreenActual

open LeanFormal.IUT

universe u

theorem treeH5InterfaceGreen_bundle {X : Type u} (W : IQHullLogVolumeInterface X) :
    HullDeterminantLogVolumeFrozenSpec ∧ W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetTensorBundleActual.h5_frozenSpec,
    LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual.treeHullFacts_interface W |>.1,
    LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual.treeHullFacts_interface W |>.2⟩

def treeH5InterfaceGreenRows : List (String × String × String) :=
  [ ("H5 frozen + interface bundle", "PROVED", "treeH5InterfaceGreen_bundle") ]

theorem treeH5InterfaceGreenRows_length : treeH5InterfaceGreenRows.length = 1 := rfl

#check treeH5InterfaceGreen_bundle
#check treeH5InterfaceGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeH5InterfaceGreenActual
end