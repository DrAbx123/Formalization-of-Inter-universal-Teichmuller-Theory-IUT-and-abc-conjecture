import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 green certificate all-routes; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeGreenCertificateAllActualAdapted

open LeanFormal.IUT

theorem treeGreenCertAll (contract : StepXIContract) :
    Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.arithmeticTeichmuller, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.sarkisyanErdosKac, contract := contract } : Cor312RouteCertificate).contract ∧
      (0 < -contract.qSigned) :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 _ contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 _ contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 _ contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_q_positive contract⟩

def treeGreenCertAllRows : List (String × String × String) :=
  [ ("all-routes certificates + q-positive", "PROVED", "treeGreenCertAll") ]

theorem treeGreenCertAllRows_length : treeGreenCertAllRows.length = 1 := rfl

#check treeGreenCertAll
#check treeGreenCertAllRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeGreenCertificateAllActualAdapted
end