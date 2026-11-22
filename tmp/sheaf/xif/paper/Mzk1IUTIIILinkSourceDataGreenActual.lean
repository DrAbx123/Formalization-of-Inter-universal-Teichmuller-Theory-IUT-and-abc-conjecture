import tmp.sheaf.xif.paper.Mzk1IUTIIILinkActual
import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import LeanFormal.IUT.IUTIII.Corollary312.Routes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # IUTII link source data green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkSourceDataGreenActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual

def linkSourceDataGreen (L : IUTIIToStepXILink) : StepXIContractSourceData :=
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

theorem iutiiiLinkSourceDataGreen_cor312 (L : IUTIIToStepXILink) :
    Cor312Conclusion (linkSourceDataGreen L).toContract := sourceData_cor312 (linkSourceDataGreen L)

theorem iutiiiLinkSourceDataGreen_route (L : IUTIIToStepXILink) :
    Cor312Conclusion (sourceData_routeCertificate Cor312Route.mochizuki3115 (linkSourceDataGreen L)).contract :=
  sourceData_routeCertificate_conclusion _ (linkSourceDataGreen L)

def iutiiiLinkSourceDataGreenRows : List (String × String × String) :=
  [ ("link source data -> contract", "PROVED", "iutiiiLinkSourceDataGreen_cor312"),
    ("link source data -> route certificate", "PROVED", "iutiiiLinkSourceDataGreen_route") ]

theorem iutiiiLinkSourceDataGreenRows_length : iutiiiLinkSourceDataGreenRows.length = 2 := rfl

#check iutiiiLinkSourceDataGreen_cor312
#check iutiiiLinkSourceDataGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkSourceDataGreenActual
end