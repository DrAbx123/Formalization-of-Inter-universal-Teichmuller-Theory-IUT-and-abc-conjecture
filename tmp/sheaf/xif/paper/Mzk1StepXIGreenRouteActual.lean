import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import tmp.sheaf.xif.paper.Mzk1Cor312ObligationConsumerActual
import LeanFormal.IUT.IUTIII.Corollary312.Routes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green route bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenRouteActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual

theorem stepXIGreenRoute_bundle (S : StepXIContractSourceData) :
    Cor312Conclusion S.toContract ∧
      Cor312Conclusion (sourceData_routeCertificate Cor312Route.mochizuki3115 S).contract ∧
      ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨sourceData_cor312 S, sourceData_routeCertificate_conclusion _ S, ipl_id, she_id, apt_id⟩

def stepXIGreenRouteRows : List (String × String × String) :=
  [ ("contract + route certificate", "PROVED", "stepXIGreenRoute_bundle"),
    ("obligation ids", "PROVED", "ipl_id/she_id/apt_id") ]

theorem stepXIGreenRouteRows_length : stepXIGreenRouteRows.length = 2 := rfl

#check stepXIGreenRoute_bundle
#check stepXIGreenRouteRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenRouteActual
end