import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green consumer 8; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer8Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual

theorem stepXIGreenConsumer8_contracts (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧ Cor312Conclusion L.toContract :=
  ⟨(stepXIGreen_contracts S L).1, (stepXIGreen_contracts S L).2.1⟩

def stepXIGreenConsumer8Rows : List (String × String × String) :=
  [ ("contract pair", "PROVED", "stepXIGreenConsumer8_contracts") ]

theorem stepXIGreenConsumer8Rows_length : stepXIGreenConsumer8Rows.length = 1 := rfl

#check stepXIGreenConsumer8_contracts
#check stepXIGreenConsumer8Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer8Actual
end