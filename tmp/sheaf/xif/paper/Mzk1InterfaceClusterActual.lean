import tmp.sheaf.xif.paper.Mzk1StepXIInterfaceConsumerActual
import tmp.sheaf.xif.paper.Mzk1BridgeInterfaceConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # iutiv interface cluster; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1InterfaceClusterActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIInterfaceConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1BridgeInterfaceConsumerActual

theorem interfaceCluster_bundle (contract : StepXIContract)
    (D : Cor312ToABCBridgeInterface) :
    Cor312Conclusion contract ∧ ABCConjecture :=
  ⟨(stepXIInterfaceConsumer_bundle contract Cor312Route.mochizuki3115).1,
    bridgeInterfaceConsumer_abc D⟩

def interfaceClusterRows : List (String × String × String) :=
  [ ("contract + interface->ABC", "PROVED (conditional)", "interfaceCluster_bundle") ]

theorem interfaceClusterRows_length : interfaceClusterRows.length = 1 := rfl

#check interfaceCluster_bundle
#check interfaceClusterRows_length

end LeanFormal.IUT.XiFPaper.Mzk1InterfaceClusterActual
end