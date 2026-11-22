import tmp.sheaf.xif.paper.Mzk1TreeH5GreenConsumerActual
import tmp.sheaf.xif.paper.Mzk1IQHullConsumerActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainIQHullTreeActualAdapted (adapted copy, A475 reuse) — chained IQHull/tree-H5 consumers

Chains EXIT0 IQHull consumer facts and the tree H5 green bundle: for a carrier W,
the image-set containment, hull finiteness and frozen determinant spec are exposed
together.  No new math; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainIQHullTreeActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1TreeH5GreenConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1IQHullConsumerActual

universe u

theorem iqHull_tree_chain {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ ∧
      HullDeterminantLogVolumeFrozenSpec :=
  treeH5Green_bundle W

theorem iqHull_tree_chain_interface {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ :=
  iqHull_bundle W

def chainIQHullTreeRows : List (String × String × String) :=
  [ ("IQHull + tree H5 bundle", "iqHull_tree_chain", "PROVED (reuse)"),
    ("IQHull interface facts", "iqHull_tree_chain_interface", "PROVED (reuse)"),
    ("scope", "interfaces only; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem chainIQHullTreeRows_length : chainIQHullTreeRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ChainIQHullTreeActualAdapted

end
