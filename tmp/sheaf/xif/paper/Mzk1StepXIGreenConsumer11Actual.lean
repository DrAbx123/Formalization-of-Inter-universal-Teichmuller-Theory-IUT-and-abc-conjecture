import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green consumer 11; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer11Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual

theorem stepXIGreenConsumer11_last (S : LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual.StepXIContractSourceData)
    (L : LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual.IUTIIToStepXILink) :
    LeanFormal.IUT.Audit.apt.id = "IUT-III.APT" :=
  (stepXIGreen_ids).2.2.1

def stepXIGreenConsumer11Rows : List (String × String × String) :=
  [ ("APT id", "PROVED", "stepXIGreenConsumer11_last") ]

theorem stepXIGreenConsumer11Rows_length : stepXIGreenConsumer11Rows.length = 1 := rfl

#check stepXIGreenConsumer11_last
#check stepXIGreenConsumer11Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer11Actual
end