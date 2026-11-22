import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green consumer 6; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer6Actual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual

theorem stepXIGreenConsumer6_bundle :
    ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨(stepXIGreen_ids).1, (stepXIGreen_ids).2.1, (stepXIGreen_ids).2.2.1⟩

def stepXIGreenConsumer6Rows : List (String × String × String) :=
  [ ("obligation ids", "PROVED", "stepXIGreenConsumer6_bundle") ]

theorem stepXIGreenConsumer6Rows_length : stepXIGreenConsumer6Rows.length = 1 := rfl

#check stepXIGreenConsumer6_bundle
#check stepXIGreenConsumer6Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer6Actual
end