import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import tmp.sheaf.xif.paper.Mzk1IUTIIILinkActual
import tmp.sheaf.xif.paper.Mzk1Cor312ObligationConsumerActual
import LeanFormal.IUT.IUTIII.Corollary312.Routes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI all-source bundles (green deps); no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIAllSourceBundlesActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual

theorem stepXI_allSources_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧
      Cor312Conclusion L.toContract ∧
      (0 < -S.toContract.qSigned) ∧
      ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨sourceData_cor312 S, cor312Conclusion_of_IUTIIToStepXILink L,
    sourceData_q_positive S, ipl_id, she_id, apt_id⟩

theorem stepXI_allSources_certificates (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion (sourceData_routeCertificate Cor312Route.mochizuki3115 S).contract ∧
      Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := L.toContract } : Cor312RouteCertificate).contract :=
  ⟨sourceData_routeCertificate_conclusion _ S,
    ({ route := Cor312Route.mochizuki3115, contract := L.toContract } : Cor312RouteCertificate).conclusion⟩

def stepXIAllSourcesRows : List (String × String × String) :=
  [ ("source-data and link contracts conclude Cor312", "PROVED", "stepXI_allSources_bundle"),
    ("both source kinds yield route certificates", "PROVED", "stepXI_allSources_certificates"),
    ("obligation ids", "PROVED", "ipl_id/she_id/apt_id"),
    ("source-data construction / ipl/she/apt proofs", "NAMED", "tree Obligations") ]

theorem stepXIAllSourcesRows_length : stepXIAllSourcesRows.length = 4 := rfl

#check stepXI_allSources_bundle
#check stepXIAllSourcesRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIAllSourceBundlesActual
end