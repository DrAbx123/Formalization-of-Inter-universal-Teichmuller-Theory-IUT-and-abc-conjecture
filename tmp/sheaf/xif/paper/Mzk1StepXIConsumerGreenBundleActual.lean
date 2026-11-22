import tmp.sheaf.xif.paper.Mzk1StepXIConsumerBundleActual
import tmp.sheaf.xif.paper.Mzk1StepXIAllSourceBundlesActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI consumer green bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIConsumerGreenBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIConsumerBundleActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual

theorem stepXIConsumerGreen_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧ Cor312Conclusion L.toContract ∧
      ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨sourceData_cor312 S, cor312Conclusion_of_IUTIIToStepXILink L, ipl_id, she_id, apt_id⟩

def stepXIConsumerGreenRows : List (String × String × String) :=
  [ ("both contracts + obligations", "PROVED", "stepXIConsumerGreen_bundle") ]

theorem stepXIConsumerGreenRows_length : stepXIConsumerGreenRows.length = 1 := rfl

#check stepXIConsumerGreen_bundle
#check stepXIConsumerGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIConsumerGreenBundleActual
end