import tmp.sheaf.xif.paper.Mzk1TreeH5DetTensorBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeHullInterfaceFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Mzk1HullTreeH5H7ConsumerBatchActualAdapted — tree H5/H7 consumer batch

A473: real Lean consumer batch over the green tree H5 files (frozen det spec,
hull interface facts). No sorry/axioms; no closure claim. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullTreeH5H7ConsumerBatchActualAdapted

open LeanFormal.IUT

universe u

theorem treeH5H7Batch_frozen : HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetTensorBundleActual.h5_frozenSpec

theorem treeH5H7Batch_hullFacts {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual.treeHullFacts_interface W

def treeH5H7BatchRows : List (String × String × String) :=
  [ ("frozen det spec", "PROVED", "treeH5H7Batch_frozen"),
    ("hull facts", "PROVED", "treeH5H7Batch_hullFacts") ]

theorem treeH5H7BatchRows_length : treeH5H7BatchRows.length = 2 := rfl

#check treeH5H7Batch_frozen
#check treeH5H7BatchRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HullTreeH5H7ConsumerBatchActualAdapted
end