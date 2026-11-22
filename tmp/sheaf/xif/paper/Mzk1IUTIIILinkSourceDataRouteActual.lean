import tmp.sheaf.xif.paper.Mzk1IUTIIILinkActual
import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import LeanFormal.IUT.IUTIII.Corollary312.Routes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # IUTII link -> typed StepXI source data -> route certificates (green deps); no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkSourceDataRouteActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual

def linkSourceData (L : IUTIIToStepXILink) : StepXIContractSourceData :=
  { qSigned := L.qSigned
    thetaSigned := L.thetaSigned
    targetSigned := L.targetSigned
    q_negative := L.q_negative
    q_le_target := L.q_le_target
    target_le_theta := L.target_le_theta
    iplProp := L.iplProp
    sheProp := L.sheProp
    aptProp := L.aptProp
    ipl_evidence := L.ipl_evidence
    she_evidence := L.she_evidence
    apt_evidence := L.apt_evidence }

theorem linkSourceData_cor312 (L : IUTIIToStepXILink) :
    Cor312Conclusion linkSourceData L.toContract := sourceData_cor312 linkSourceData L

theorem linkSourceData_allRoutes (L : IUTIIToStepXILink) :
    Cor312Conclusion (sourceData_routeCertificate Cor312Route.mochizuki3115 linkSourceData L).contract ∧
      Cor312Conclusion (sourceData_routeCertificate Cor312Route.arithmeticTeichmuller linkSourceData L).contract ∧
      Cor312Conclusion (sourceData_routeCertificate Cor312Route.sarkisyanErdosKac linkSourceData L).contract :=
  ⟨sourceData_routeCertificate_conclusion _ linkSourceData L,
    sourceData_routeCertificate_conclusion _ linkSourceData L,
    sourceData_routeCertificate_conclusion _ linkSourceData L⟩

def linkSourceDataRouteRows : List (String × String × String) :=
  [ ("link -> source data", "PROVED", "linkSourceData"),
    ("link source data -> Cor312", "PROVED", "linkSourceData_cor312"),
    ("all routes from link", "PROVED", "linkSourceData_allRoutes") ]

theorem linkSourceDataRouteRows_length : linkSourceDataRouteRows.length = 3 := rfl

#check linkSourceData_allRoutes
#check linkSourceDataRouteRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkSourceDataRouteActual
end