import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # iutiv-abc:G3 real-line reduction consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FrontierRealLineConsumerActual

open LeanFormal.IUT

def frontierRealLine_consumer (h : ABCFrontierRealLine) : ABCFrontier.{0} :=
  ABCFrontier.reduce_realLine h

theorem frontierRealLine_abc (h : ABCFrontierRealLine) : ABCConjecture :=
  abcConjecture_of_frontier.{0} (frontierRealLine_consumer h)

def frontierRealLineConsumerRows : List (String × String × String) :=
  [ ("real-line reduction", "PROVED (conditional)", "frontierRealLine_consumer"),
    ("real-line frontier -> ABC", "PROVED (conditional)", "frontierRealLine_abc"),
    ("ABCFrontier clauses", "NAMED", "F4/F5 remain open") ]

theorem frontierRealLineConsumerRows_length : frontierRealLineConsumerRows.length = 3 := rfl

#check frontierRealLine_abc
#check frontierRealLineConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1FrontierRealLineConsumerActual
end