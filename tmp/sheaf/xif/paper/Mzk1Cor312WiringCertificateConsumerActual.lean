import tmp.sheaf.xif.paper.Mzk1Cor312TargetWiringActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Cor312 wiring certificate consumer (green dep); no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312WiringCertificateConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312TargetWiringActual

theorem wiring_certificate_exists (route : Cor312Route) (contract : StepXIContract) :
    ∃ certificate : Cor312RouteCertificate,
      certificate.route = route ∧ certificate.contract = contract ∧
      Cor312Conclusion certificate.contract :=
  ⟨certificateOfContract route contract, rfl, rfl, certificate_conclusion _⟩

theorem wiring_allRoutes (contract : StepXIContract) :
    Cor312Conclusion (certificateOfContract Cor312Route.mochizuki3115 contract).contract ∧
      Cor312Conclusion (certificateOfContract Cor312Route.arithmeticTeichmuller contract).contract ∧
      Cor312Conclusion (certificateOfContract Cor312Route.sarkisyanErdosKac contract).contract :=
  all_routes_conclusion contract

def wiringCertificateRows : List (String × String × String) :=
  [ ("certificate existence from wiring", "PROVED", "wiring_certificate_exists"),
    ("all-routes conclusions", "PROVED", "wiring_allRoutes") ]

theorem wiringCertificateRows_length : wiringCertificateRows.length = 2 := rfl

#check wiring_certificate_exists
#check wiringCertificateRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Cor312WiringCertificateConsumerActual
end