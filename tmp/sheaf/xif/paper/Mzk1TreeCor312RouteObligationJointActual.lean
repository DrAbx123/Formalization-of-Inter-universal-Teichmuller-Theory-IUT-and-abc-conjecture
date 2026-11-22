import LeanFormal.IUT.IUTIII.Corollary312.Routes
import LeanFormal.IUT.IUTIII.Corollary312.Obligations

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree-only Cor312 route+obligation joint; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312RouteObligationJointActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit

theorem tree_routeObligation_bundle (certificate : Cor312RouteCertificate) :
    Cor312Conclusion certificate.contract ∧
      ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" ∧
      ipl.dependsOn = ["IUT-III.theorem-3.11-output", "IUT-III.Ind1", "IUT-III.Ind2"] :=
  ⟨certificate.conclusion, rfl, rfl, rfl, rfl⟩

theorem tree_routeObligation_allRoutes (contract : StepXIContract) :
    Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.arithmeticTeichmuller, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.sarkisyanErdosKac, contract := contract } : Cor312RouteCertificate).contract :=
  ⟨({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).conclusion,
    ({ route := Cor312Route.arithmeticTeichmuller, contract := contract } : Cor312RouteCertificate).conclusion,
    ({ route := Cor312Route.sarkisyanErdosKac, contract := contract } : Cor312RouteCertificate).conclusion⟩

def treeRouteObligationRows : List (String × String × String) :=
  [ ("route certificate + obligation ids", "PROVED", "tree_routeObligation_bundle"),
    ("all-routes certificates", "PROVED", "tree_routeObligation_allRoutes") ]

theorem treeRouteObligationRows_length : treeRouteObligationRows.length = 2 := rfl

#check tree_routeObligation_bundle
#check treeRouteObligationRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312RouteObligationJointActual
end