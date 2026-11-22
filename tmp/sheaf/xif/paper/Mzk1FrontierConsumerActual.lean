import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # iutiv-abc:G3 frontier consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FrontierConsumerActual

open LeanFormal.IUT

def frontierConsumer_bridge (h : ABCFrontier) : Cor312ToABCBridgeInterface :=
  bridgeInterface_of_frontier h

theorem frontierConsumer_abc (h : ABCFrontier) : ABCConjecture :=
  abcConjecture_of_frontier h

def frontierConsumerRows : List (String × String × String) :=
  [ ("frontier -> bridge interface", "PROVED (conditional)", "frontierConsumer_bridge"),
    ("frontier -> ABC", "PROVED (conditional)", "frontierConsumer_abc"),
    ("ABCFrontier clauses F4/F5", "NAMED", "the two comparison clauses remain open") ]

theorem frontierConsumerRows_length : frontierConsumerRows.length = 3 := rfl

#check frontierConsumer_abc
#check frontierConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1FrontierConsumerActual
end