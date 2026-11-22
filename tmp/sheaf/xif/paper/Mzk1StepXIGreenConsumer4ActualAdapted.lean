import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual
import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumer2Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green consumer 4; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer4ActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual

theorem stepXIGreenConsumer4_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    (0 < -S.toContract.qSigned) ∧ (0 < -L.toContract.qSigned) :=
  ⟨(stepXIGreen_contracts S L).2.2.1, (stepXIGreen_contracts S L).2.2.2⟩

def stepXIGreenConsumer4Rows : List (String × String × String) :=
  [ ("q-positive pair", "PROVED", "stepXIGreenConsumer4_bundle") ]

theorem stepXIGreenConsumer4Rows_length : stepXIGreenConsumer4Rows.length = 1 := rfl

#check stepXIGreenConsumer4_bundle
#check stepXIGreenConsumer4Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer4ActualAdapted
end