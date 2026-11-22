import tmp.sheaf.xif.paper.Mzk1TreeH5DetTensorBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeStepXIBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual
import LeanFormal.IUT.IUTIII.Corollary312.Obligations

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree green bundles consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeGreenBundlesConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Audit

universe u

theorem treeGreen_bundle {X : Type u} (W : IQHullLogVolumeInterface X)
    (contract : StepXIContract) (route : Cor312Route) :
    HullDeterminantLogVolumeFrozenSpec ∧
      Cor312Conclusion contract ∧
      ipl.id = "IUT-III.IPL" :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetTensorBundleActual.h5_frozenSpec,
    (LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIBundleActual.stepXI_contract_bundle contract route).1,
    by rfl⟩

theorem treeGreen_allRoutes (contract : StepXIContract) :
    Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.arithmeticTeichmuller, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.sarkisyanErdosKac, contract := contract } : Cor312RouteCertificate).contract :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_all_routes_cor312 contract

def treeGreenRows : List (String × String × String) :=
  [ ("frozen det + contract bundle", "PROVED", "treeGreen_bundle"),
    ("all routes", "PROVED", "treeGreen_allRoutes") ]

theorem treeGreenRows_length : treeGreenRows.length = 2 := rfl

#check treeGreen_bundle
#check treeGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeGreenBundlesConsumerActualAdapted
end