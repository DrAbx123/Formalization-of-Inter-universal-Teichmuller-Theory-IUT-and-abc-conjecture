import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green consumer 10; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer10Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual

theorem stepXIGreenConsumer10_firstContract (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract :=
  (stepXIGreen_contracts S L).1

def stepXIGreenConsumer10Rows : List (String × String × String) :=
  [ ("first contract", "PROVED", "stepXIGreenConsumer10_firstContract") ]

theorem stepXIGreenConsumer10Rows_length : stepXIGreenConsumer10Rows.length = 1 := rfl

#check stepXIGreenConsumer10_firstContract
#check stepXIGreenConsumer10Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer10Actual
end