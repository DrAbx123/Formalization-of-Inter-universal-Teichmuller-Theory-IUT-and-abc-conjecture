import tmp.sheaf.xif.paper.Mzk1StepXIGreenClusterRollupActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI green cluster 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenCluster2Actual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenClusterRollupActual

theorem stepXIGreenCluster2_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧ ipl.id = "IUT-III.IPL" :=
  ⟨(stepXIGreenClusterRollup_bundle S L).1, (stepXIGreenClusterRollup_bundle S L).2.2.1⟩

def stepXIGreenCluster2Rows : List (String × String × String) :=
  [ ("contract + IPL", "PROVED", "stepXIGreenCluster2_bundle") ]

theorem stepXIGreenCluster2Rows_length : stepXIGreenCluster2Rows.length = 1 := rfl

#check stepXIGreenCluster2_bundle
#check stepXIGreenCluster2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenCluster2Actual
end