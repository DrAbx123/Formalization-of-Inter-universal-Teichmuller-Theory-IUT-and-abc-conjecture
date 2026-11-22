import tmp.sheaf.xif.paper.Mzk1Cor312WiringCertificateConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Cor312 wiring green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312WiringGreenConsumerActual

open LeanFormal.IUT

theorem cor312WiringGreen_certificate (route : Cor312Route) (contract : StepXIContract) :
    ∃ certificate : Cor312RouteCertificate,
      certificate.route = route ∧ certificate.contract = contract ∧
      Cor312Conclusion certificate.contract :=
  LeanFormal.IUT.XiFPaper.Mzk1Cor312WiringCertificateConsumerActual.wiring_certificate_exists route contract

theorem cor312WiringGreen_allRoutes (contract : StepXIContract) :
    Cor312Conclusion (LeanFormal.IUT.XiFPaper.Mzk1Cor312WiringCertificateConsumerActual.certificateOfContract Cor312Route.mochizuki3115 contract).contract :=
  (LeanFormal.IUT.XiFPaper.Mzk1Cor312WiringCertificateConsumerActual.wiring_allRoutes contract).1

def cor312WiringGreenRows : List (String × String × String) :=
  [ ("certificate existence", "PROVED", "cor312WiringGreen_certificate"),
    ("all-routes first", "PROVED", "cor312WiringGreen_allRoutes") ]

theorem cor312WiringGreenRows_length : cor312WiringGreenRows.length = 2 := rfl

#check cor312WiringGreen_certificate
#check cor312WiringGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Cor312WiringGreenConsumerActual
end