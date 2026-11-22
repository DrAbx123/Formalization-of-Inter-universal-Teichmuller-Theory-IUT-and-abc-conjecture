import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual
import tmp.sheaf.xif.paper.Mzk1StepXIAllSourceBundlesActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green consumer 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer2Actual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual

theorem stepXIGreenConsumer2_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧ Cor312Conclusion L.toContract ∧
      (0 < -S.toContract.qSigned) ∧ (0 < -L.toContract.qSigned) :=
  stepXIGreen_contracts S L

theorem stepXIGreenConsumer2_obligations :
    ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨stepXIGreen_ids.1, stepXIGreen_ids.2.1, stepXIGreen_ids.2.2.1⟩

def stepXIGreenConsumer2Rows : List (String × String × String) :=
  [ ("contracts + q-positive", "PROVED", "stepXIGreenConsumer2_bundle"),
    ("obligations", "PROVED", "stepXIGreenConsumer2_obligations") ]

theorem stepXIGreenConsumer2Rows_length : stepXIGreenConsumer2Rows.length = 2 := rfl

#check stepXIGreenConsumer2_bundle
#check stepXIGreenConsumer2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer2Actual
end