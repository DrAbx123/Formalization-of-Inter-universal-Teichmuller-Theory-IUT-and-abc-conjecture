import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual
import tmp.sheaf.xif.paper.Mzk1StepXIConsumerBundleActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green consumer 5; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer5Actual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual

theorem stepXIGreenConsumer5_bundle (S : StepXIContractSourceData) :
    ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨(stepXIGreen_ids).1, (stepXIGreen_ids).2.1, (stepXIGreen_ids).2.2.1⟩

def stepXIGreenConsumer5Rows : List (String × String × String) :=
  [ ("obligation ids", "PROVED", "stepXIGreenConsumer5_bundle") ]

theorem stepXIGreenConsumer5Rows_length : stepXIGreenConsumer5Rows.length = 1 := rfl

#check stepXIGreenConsumer5_bundle
#check stepXIGreenConsumer5Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer5Actual
end