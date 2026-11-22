import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import tmp.sheaf.xif.paper.Mzk1Cor312ObligationConsumerActual
import tmp.sheaf.xif.paper.Mzk1IUTIIILinkActual
import LeanFormal.IUT.IUTIII.Corollary312.Routes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI cluster rollup; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIClusterRollupActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual

theorem stepXIClusterRollup_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧ Cor312Conclusion L.toContract ∧
      Cor312Conclusion (sourceData_routeCertificate Cor312Route.mochizuki3115 S).contract ∧
      ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨sourceData_cor312 S, cor312Conclusion_of_IUTIIToStepXILink L,
    sourceData_routeCertificate_conclusion _ S, ipl_id, she_id, apt_id⟩

def stepXIClusterRollupRows : List (String × String × String) :=
  [ ("contracts + route + obligations", "PROVED", "stepXIClusterRollup_bundle") ]

theorem stepXIClusterRollupRows_length : stepXIClusterRollupRows.length = 1 := rfl

#check stepXIClusterRollup_bundle
#check stepXIClusterRollupRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIClusterRollupActual
end