import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green consumer 9; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer9Actual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual

theorem stepXIGreenConsumer9_ids :
    ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" :=
  ⟨(stepXIGreen_ids).1, (stepXIGreen_ids).2.1⟩

def stepXIGreenConsumer9Rows : List (String × String × String) :=
  [ ("IPL/SHE ids", "PROVED", "stepXIGreenConsumer9_ids") ]

theorem stepXIGreenConsumer9Rows_length : stepXIGreenConsumer9Rows.length = 1 := rfl

#check stepXIGreenConsumer9_ids
#check stepXIGreenConsumer9Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer9Actual
end