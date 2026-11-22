import tmp.sheaf.xif.paper.Mzk1StepXIInterfaceConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # StepXI interface cluster; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIInterfaceClusterActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIInterfaceConsumerActual

theorem stepXIInterfaceCluster_bundle (contract : StepXIContract) (route : Cor312Route) :
    Cor312Conclusion contract ∧ (0 < -contract.qSigned) :=
  ⟨(stepXIInterfaceConsumer_bundle contract route).1, stepXIInterfaceConsumer_qpositive contract⟩

def stepXIInterfaceClusterRows : List (String × String × String) :=
  [ ("contract + q", "PROVED", "stepXIInterfaceCluster_bundle") ]

theorem stepXIInterfaceClusterRows_length : stepXIInterfaceClusterRows.length = 1 := rfl

#check stepXIInterfaceCluster_bundle
#check stepXIInterfaceClusterRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIInterfaceClusterActualAdapted
end