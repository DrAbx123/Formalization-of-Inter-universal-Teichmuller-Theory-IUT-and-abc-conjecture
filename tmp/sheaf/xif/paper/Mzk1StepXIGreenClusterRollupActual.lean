import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual
import tmp.sheaf.xif.paper.Mzk1StepXIContractGreenConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green cluster rollup; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenClusterRollupActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual

theorem stepXIGreenClusterRollup_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧ Cor312Conclusion L.toContract ∧
      ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual.stepXIGreen_contracts S L |>.1,
    LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual.stepXIGreen_contracts S L |>.2.1,
    LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual.stepXIGreen_ids |>.1,
    LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual.stepXIGreen_ids |>.2.1,
    LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual.stepXIGreen_ids |>.2.2.1⟩

def stepXIGreenClusterRollupRows : List (String × String × String) :=
  [ ("contracts + obligations", "PROVED", "stepXIGreenClusterRollup_bundle") ]

theorem stepXIGreenClusterRollupRows_length : stepXIGreenClusterRollupRows.length = 1 := rfl

#check stepXIGreenClusterRollup_bundle
#check stepXIGreenClusterRollupRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenClusterRollupActual
end