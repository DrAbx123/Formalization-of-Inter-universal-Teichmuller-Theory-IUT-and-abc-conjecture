import tmp.sheaf.xif.paper.Mzk1TreeH5DetTensorBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeIQHullFactsActual
import tmp.sheaf.xif.paper.Mzk1TreeStepXIBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree cluster rollup; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeClusterRollupActual

open LeanFormal.IUT

universe u

theorem treeClusterRollup_hull {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ :=
  ⟨W.imageSet_subset_hull, W.hull_logVolume_lt_top⟩

theorem treeClusterRollup_contract (contract : StepXIContract) (route : Cor312Route) :
    Cor312Conclusion contract ∧
      Cor312Conclusion ({ route := route, contract := contract } : Cor312RouteCertificate).contract :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIBundleActual.stepXI_contract_bundle contract route |>.1,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 route contract⟩

theorem treeClusterRollup_frozen : HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetTensorBundleActual.h5_frozenSpec

def treeClusterRollupRows : List (String × String × String) :=
  [ ("hull facts", "PROVED", "treeClusterRollup_hull"),
    ("contract + route", "PROVED", "treeClusterRollup_contract"),
    ("frozen det spec", "PROVED", "treeClusterRollup_frozen") ]

theorem treeClusterRollupRows_length : treeClusterRollupRows.length = 3 := rfl

#check treeClusterRollup_contract
#check treeClusterRollupRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeClusterRollupActual
end