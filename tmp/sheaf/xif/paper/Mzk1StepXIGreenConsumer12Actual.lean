import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green consumer 12; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer12Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual

theorem stepXIGreenConsumer12_second (S : LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual.StepXIContractSourceData)
    (L : LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual.IUTIIToStepXILink) :
    Cor312Conclusion L.toContract :=
  (stepXIGreen_contracts S L).2.1

def stepXIGreenConsumer12Rows : List (String × String × String) :=
  [ ("link contract", "PROVED", "stepXIGreenConsumer12_second") ]

theorem stepXIGreenConsumer12Rows_length : stepXIGreenConsumer12Rows.length = 1 := rfl

#check stepXIGreenConsumer12_second
#check stepXIGreenConsumer12Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer12Actual
end