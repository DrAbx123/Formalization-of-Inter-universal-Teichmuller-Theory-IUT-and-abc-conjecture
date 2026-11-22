import tmp.sheaf.xif.paper.Mzk1StepXIContractAssemblyActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312GreenFactsConsumer3Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainStepXIConsumerActualAdapted (adapted copy, A475 reuse) — chained StepXI/Cor312 consumers

Chains EXIT0 assets: numeric source data -> assembled StepXIContract -> ordered
Cor312 conclusion, q-positivity and routed certificate conclusion.  No new math;
no closure; gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainStepXIConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsConsumer3Actual

/-- From numeric source data to the full ordered/routed contract bundle. -/
theorem chain_from_data (q theta target : ℝ) (hq : q < 0)
    (hqt : q ≤ target) (htt : target ≤ theta) {ipl she apt : Prop}
    (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion (assembleStepXIContract q theta target hq hqt htt hipl hshe hapt) ∧
      (0 < -(assembleStepXIContract q theta target hq hqt htt hipl hshe hapt).qSigned) ∧
      Cor312Conclusion
        ({ route := Cor312Route.mochizuki3115,
           contract := assembleStepXIContract q theta target hq hqt htt hipl hshe hapt } :
          Cor312RouteCertificate).contract :=
  treeCor312GreenFactsConsumer3_bundle
    (assembleStepXIContract q theta target hq hqt htt hipl hshe hapt)

def chainStepXIRows : List (String × String × String) :=
  [ ("data -> full contract bundle", "chain_from_data", "PROVED (reuse)"),
    ("scope", "source data explicit; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem chainStepXIRows_length : chainStepXIRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ChainStepXIConsumerActualAdapted

end
