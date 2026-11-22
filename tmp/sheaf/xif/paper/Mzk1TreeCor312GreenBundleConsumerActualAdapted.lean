import tmp.sheaf.xif.paper.Mzk1TreeCor312GreenFactsConsumer3Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1TreeCor312GreenBundleConsumerActualAdapted (adapted copy, A475 reuse) — tree Cor312 green-bundle consumer

Reuses the EXIT0 tree Cor312 green-facts bundle: a StepXIContract gives the
ordered Cor312 conclusion, q-positivity and the routed certificate conclusion.
No new math; contract explicit; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenBundleConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsConsumer3Actual

theorem treeCor312_bundle_consumer (contract : StepXIContract) :
    Cor312Conclusion contract ∧ (0 < -contract.qSigned) ∧
      Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } :
        Cor312RouteCertificate).contract :=
  treeCor312GreenFactsConsumer3_bundle contract

def treeCor312GreenBundleRows : List (String × String × String) :=
  [ ("green bundle", "treeCor312_bundle_consumer", "PROVED (reuse)"),
    ("scope", "contract explicit; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem treeCor312GreenBundleRows_length : treeCor312GreenBundleRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenBundleConsumerActualAdapted

end
