import tmp.sheaf.xif.paper.Mzk1TreeH5InterfaceGreenActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree H5 interface consumer 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeH5InterfaceConsumer2Actual

open LeanFormal.IUT

universe u

theorem treeH5InterfaceConsumer2_bundle {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ :=
  have h := LeanFormal.IUT.XiFPaper.Mzk1TreeH5InterfaceGreenActual.treeH5InterfaceGreen_bundle W
  ⟨h.2.1, h.2.2⟩

def treeH5InterfaceConsumer2Rows : List (String × String × String) :=
  [ ("image subset + finite", "PROVED", "treeH5InterfaceConsumer2_bundle") ]

theorem treeH5InterfaceConsumer2Rows_length : treeH5InterfaceConsumer2Rows.length = 1 := rfl

#check treeH5InterfaceConsumer2_bundle
#check treeH5InterfaceConsumer2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeH5InterfaceConsumer2Actual
end