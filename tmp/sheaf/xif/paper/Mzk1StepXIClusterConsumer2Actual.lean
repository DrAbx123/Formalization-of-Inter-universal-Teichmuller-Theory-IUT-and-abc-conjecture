import tmp.sheaf.xif.paper.Mzk1StepXIClusterRollupActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI cluster consumer 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIClusterConsumer2Actual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIClusterRollupActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual

theorem stepXIClusterConsumer2_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧ ipl.id = "IUT-III.IPL" :=
  ⟨(stepXIClusterRollup_bundle S L).1, (stepXIClusterRollup_bundle S L).2.2.2.1⟩

def stepXIClusterConsumer2Rows : List (String × String × String) :=
  [ ("contract + IPL", "PROVED", "stepXIClusterConsumer2_bundle") ]

theorem stepXIClusterConsumer2Rows_length : stepXIClusterConsumer2Rows.length = 1 := rfl

#check stepXIClusterConsumer2_bundle
#check stepXIClusterConsumer2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIClusterConsumer2Actual
end