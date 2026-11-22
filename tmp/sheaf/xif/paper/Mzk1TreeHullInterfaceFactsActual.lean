import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree-only H5 interface + det frozen facts; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual

open LeanFormal.IUT

universe u

theorem treeHullFacts_interface {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ :=
  ⟨W.imageSet_subset_hull, W.hull_logVolume_lt_top⟩

theorem treeHullFacts_frozen : HullDeterminantLogVolumeFrozenSpec :=
  hullDeterminantLogVolumeFrozenSpec_holds

theorem treeHullFacts_bundle {X : Type u} (W : IQHullLogVolumeInterface X) :
    (W.imageSet ⊆ W.hull) ∧ (W.logVolume W.hull < ⊤) ∧ HullDeterminantLogVolumeFrozenSpec :=
  ⟨W.imageSet_subset_hull, W.hull_logVolume_lt_top, hullDeterminantLogVolumeFrozenSpec_holds⟩

def treeHullFactsRows : List (String × String × String) :=
  [ ("interface image subset hull + finite", "PROVED", "treeHullFacts_interface"),
    ("frozen det spec", "PROVED", "treeHullFacts_frozen"),
    ("bundle", "PROVED", "treeHullFacts_bundle") ]

theorem treeHullFactsRows_length : treeHullFactsRows.length = 3 := rfl

#check treeHullFacts_bundle
#check treeHullFactsRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual
end