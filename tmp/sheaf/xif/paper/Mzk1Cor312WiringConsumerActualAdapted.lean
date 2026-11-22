import tmp.sheaf.xif.paper.Mzk1Cor312TargetWiringActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1Cor312WiringConsumerActualAdapted (adapted copy, A475 reuse) — Cor312 route-wiring bundle consumer

Reuses the EXIT0 Mzk1Cor312TargetWiringActual (route certificates and StepXIContract
wiring) to expose the route conclusions and the q-positivity consumer.  No contract
is constructed here; the named StepXI inputs remain explicit.
No closure; gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312WiringConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312TargetWiringActual

theorem mochizuki_route_conclusion_consumer (contract : StepXIContract) :
    Cor312Conclusion contract :=
  mochizuki_route_conclusion contract

theorem all_routes_conclusion_consumer (contract : StepXIContract) :
    Cor312Conclusion contract :=
  all_routes_conclusion contract

theorem q_positive_target_consumer (contract : StepXIContract) :
    0 < -contract.qSigned :=
  q_positive_target contract

def cor312WiringConsumerRows : List (String × String × String) :=
  [ ("Mochizuki route", "mochizuki_route_conclusion_consumer", "PROVED (reuse)"),
    ("all routes", "all_routes_conclusion_consumer", "PROVED (reuse)"),
    ("q positivity", "q_positive_target_consumer", "PROVED (reuse)"),
    ("scope", "contract explicit; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem cor312WiringConsumerRows_length : cor312WiringConsumerRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Cor312WiringConsumerActualAdapted

end
