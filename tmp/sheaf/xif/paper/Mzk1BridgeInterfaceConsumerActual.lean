import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # iutiv-abc interface consumer (Cor312 -> ABC); no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1BridgeInterfaceConsumerActual

open LeanFormal.IUT

theorem bridgeInterfaceConsumer_abc (D : Cor312ToABCBridgeInterface) : ABCConjecture :=
  cor312ToABCBridge_abcConjecture D

def bridgeInterfaceConsumerRows : List (String × String × String) :=
  [ ("interface -> ABC", "PROVED (conditional)", "bridgeInterfaceConsumer_abc"),
    ("interface fields", "NAMED", "carrier/hullData/epsilonComparison supplied by frontier") ]

theorem bridgeInterfaceConsumerRows_length : bridgeInterfaceConsumerRows.length = 2 := rfl

#check bridgeInterfaceConsumer_abc
#check bridgeInterfaceConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1BridgeInterfaceConsumerActual
end