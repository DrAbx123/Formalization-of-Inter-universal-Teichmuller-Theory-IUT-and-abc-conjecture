import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual
import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumer2Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green consumer 3; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer3Actual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual

theorem stepXIGreenConsumer3_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧
      Cor312Conclusion L.toContract :=
  ⟨(stepXIGreen_contracts S L).1, (stepXIGreen_contracts S L).2.1⟩

def stepXIGreenConsumer3Rows : List (String × String × String) :=
  [ ("contracts", "PROVED", "stepXIGreenConsumer3_bundle") ]

theorem stepXIGreenConsumer3Rows_length : stepXIGreenConsumer3Rows.length = 1 := rfl

#check stepXIGreenConsumer3_bundle
#check stepXIGreenConsumer3Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer3Actual
end