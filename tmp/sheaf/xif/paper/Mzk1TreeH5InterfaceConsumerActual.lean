import tmp.sheaf.xif.paper.Mzk1TreeH5InterfaceGreenActual
import tmp.sheaf.xif.paper.Mzk1TreeHullInterfaceFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree H5 interface consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeH5InterfaceConsumerActual

open LeanFormal.IUT

universe u

theorem treeH5InterfaceConsumer_bundle {X : Type u} (W : IQHullLogVolumeInterface X) :
    HullDeterminantLogVolumeFrozenSpec ∧ W.logVolume W.hull < ⊤ :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeH5InterfaceGreenActual.treeH5InterfaceGreen_bundle W |>.1,
    LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual.treeHullFacts_interface W |>.2⟩

def treeH5InterfaceConsumerRows : List (String × String × String) :=
  [ ("frozen spec + finite hull", "PROVED", "treeH5InterfaceConsumer_bundle") ]

theorem treeH5InterfaceConsumerRows_length : treeH5InterfaceConsumerRows.length = 1 := rfl

#check treeH5InterfaceConsumer_bundle
#check treeH5InterfaceConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeH5InterfaceConsumerActual
end