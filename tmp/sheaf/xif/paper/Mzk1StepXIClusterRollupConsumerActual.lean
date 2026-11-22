import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumerActual
import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import tmp.sheaf.xif.paper.Mzk1IUTIIILinkActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI cluster rollup consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIClusterRollupConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumerActual

theorem stepXIClusterRollupConsumer_bundle (S : StepXIContractSourceData) (L : IUTIIToStepXILink) :
    Cor312Conclusion S.toContract ∧ Cor312Conclusion L.toContract :=
  ⟨(stepXIGreen_contracts S L).1, (stepXIGreen_contracts S L).2.1⟩

def stepXIClusterRollupConsumerRows : List (String × String × String) :=
  [ ("contracts", "PROVED", "stepXIClusterRollupConsumer_bundle") ]

theorem stepXIClusterRollupConsumerRows_length : stepXIClusterRollupConsumerRows.length = 1 := rfl

#check stepXIClusterRollupConsumer_bundle
#check stepXIClusterRollupConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIClusterRollupConsumerActual
end