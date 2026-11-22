import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import tmp.sheaf.xif.paper.Mzk1Cor312ObligationConsumerActual
import LeanFormal.IUT.IUTIII.Corollary312.Routes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI construction + obligation + route joint (green deps); no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIObligationRouteJointActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual

theorem stepXIObligationRoute_bundle (S : StepXIContractSourceData) :
    Cor312Conclusion S.toContract ∧ (0 < -S.toContract.qSigned) ∧
      ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" ∧
      Cor312Conclusion (sourceData_routeCertificate Cor312Route.mochizuki3115 S).contract :=
  ⟨sourceData_cor312 S, sourceData_q_positive S, ipl_id, she_id, apt_id,
    sourceData_routeCertificate_conclusion _ S⟩

def stepXIObligationRouteRows : List (String × String × String) :=
  [ ("contract conclusions", "PROVED", "sourceData_cor312/sourceData_q_positive"),
    ("obligation ids", "PROVED", "ipl_id/she_id/apt_id"),
    ("route certificate", "PROVED", "sourceData_routeCertificate_conclusion") ]

theorem stepXIObligationRouteRows_length : stepXIObligationRouteRows.length = 3 := rfl

#check stepXIObligationRoute_bundle
#check stepXIObligationRouteRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIObligationRouteJointActual
end