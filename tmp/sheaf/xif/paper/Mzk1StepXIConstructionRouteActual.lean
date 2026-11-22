import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import LeanFormal.IUT.IUTIII.Corollary312.Routes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI construction route harness; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIConstructionRouteActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual

theorem sourceData_all_routes (S : StepXIContractSourceData) :
    Cor312Conclusion (sourceData_routeCertificate Cor312Route.mochizuki3115 S).contract ∧
      Cor312Conclusion (sourceData_routeCertificate Cor312Route.arithmeticTeichmuller S).contract ∧
      Cor312Conclusion (sourceData_routeCertificate Cor312Route.sarkisyanErdosKac S).contract :=
  ⟨sourceData_routeCertificate_conclusion _ S,
    sourceData_routeCertificate_conclusion _ S,
    sourceData_routeCertificate_conclusion _ S⟩

theorem sourceData_certificate_exists (route : Cor312Route) (S : StepXIContractSourceData) :
    ∃ certificate : Cor312RouteCertificate,
      Cor312Conclusion certificate.contract :=
  ⟨sourceData_routeCertificate route S, sourceData_routeCertificate_conclusion route S⟩

def sourceDataRouteRows : List (String × String × String) :=
  [ ("all routes from source data", "PROVED", "sourceData_all_routes")
  , ("certificate existence", "PROVED", "sourceData_certificate_exists")
  , ("source data from IUT input", "NAMED", "Contract:61 Obligation") ]

theorem sourceDataRouteRows_length : sourceDataRouteRows.length = 3 := rfl

#check sourceData_all_routes
#check sourceData_certificate_exists
#check sourceDataRouteRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIConstructionRouteActual
end