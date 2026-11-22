import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312RouteAuditActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 green certificate consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenCertificateActual

open LeanFormal.IUT

theorem treeCor312GreenCert_contract (contract : StepXIContract) :
    Cor312Conclusion contract :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_contract_cor312 contract

theorem treeCor312GreenCert_route (route : Cor312Route) (contract : StepXIContract) :
    Cor312Conclusion ({ route := route, contract := contract } : Cor312RouteCertificate).contract :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_route_cor312 route contract

theorem treeCor312GreenCert_bundle (contract : StepXIContract) (route : Cor312Route) :
    Cor312Conclusion contract ∧
      Cor312Conclusion ({ route := route, contract := contract } : Cor312RouteCertificate).contract ∧
      (0 < -contract.qSigned) :=
  ⟨treeCor312GreenCert_contract contract, treeCor312GreenCert_route route contract,
    LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_q_positive contract⟩

def treeCor312GreenCertRows : List (String × String × String) :=
  [ ("contract conclusion", "PROVED", "treeCor312GreenCert_contract"),
    ("route certificate conclusion", "PROVED", "treeCor312GreenCert_route"),
    ("bundle", "PROVED", "treeCor312GreenCert_bundle") ]

theorem treeCor312GreenCertRows_length : treeCor312GreenCertRows.length = 3 := rfl

#check treeCor312GreenCert_bundle
#check treeCor312GreenCertRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenCertificateActual
end