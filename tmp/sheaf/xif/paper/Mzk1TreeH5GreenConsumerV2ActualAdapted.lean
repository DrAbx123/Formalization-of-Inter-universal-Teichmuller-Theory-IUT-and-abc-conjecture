import tmp.sheaf.xif.paper.Mzk1TreeH5GreenConsumerActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1TreeH5GreenConsumerV2ActualAdapted (adapted copy, A475 reuse) — tree H5 green bundle consumer

Reuses the EXIT0 tree H5 green consumer to expose the IQHull interface facts plus
the frozen determinant/log-volume spec bundle.  No new math; no closure; gate NOT
PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeH5GreenConsumerV2ActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1TreeH5GreenConsumerActual

universe u

theorem treeH5Green_bundle_consumer {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ ∧ HullDeterminantLogVolumeFrozenSpec :=
  treeH5Green_bundle W

def treeH5GreenConsumerV2Rows : List (String × String × String) :=
  [ ("green bundle", "treeH5Green_bundle_consumer", "PROVED (reuse)"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem treeH5GreenConsumerV2Rows_length : treeH5GreenConsumerV2Rows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1TreeH5GreenConsumerV2ActualAdapted

end
