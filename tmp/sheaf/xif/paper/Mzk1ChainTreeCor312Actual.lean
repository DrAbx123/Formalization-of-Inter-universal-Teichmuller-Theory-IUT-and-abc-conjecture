import tmp.sheaf.xif.paper.Mzk1TreeCor312GreenConsumer9Actual
import tmp.sheaf.xif.paper.Mzk1TreeCor312GreenFactsConsumer3Actual
import tmp.sheaf.xif.paper.Mzk1StepXIContractAssemblyActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainTreeCor312Actual — chained tree Cor312 consumers

Chains EXIT0 tree Cor312 green consumers 9/3 with the StepXI contract assembly:
an assembled contract gives the ordered Cor312 conclusion (two proof paths),
q-positivity and the routed certificate conclusion.  No new math; no closure.
Gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainTreeCor312Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenConsumer9Actual
open LeanFormal.IUT.XiFPaper.Mzk1TreeCor312GreenFactsConsumer3Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractAssemblyActual

/-- From numeric source data, the chained tree Cor312 bundle. -/
theorem treeCor312_chain_from_data (q theta target : ℝ) (hq : q < 0)
    (hqt : q ≤ target) (htt : target ≤ theta) {ipl she apt : Prop}
    (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion (assembleStepXIContract q theta target hq hqt htt hipl hshe hapt) ∧
      Cor312Conclusion (assembleStepXIContract q theta target hq hqt htt hipl hshe hapt) ∧
      (0 < -(assembleStepXIContract q theta target hq hqt htt hipl hshe hapt).qSigned) := by
  let C := assembleStepXIContract q theta target hq hqt htt hipl hshe hapt
  exact ⟨treeCor312GreenConsumer9_contract C,
    (treeCor312GreenFactsConsumer3_bundle C).1,
    (treeCor312GreenFactsConsumer3_bundle C).2.1⟩

def chainTreeCor312Rows : List (String × String × String) :=
  [ ("data -> chained Cor312 bundle", "treeCor312_chain_from_data", "PROVED (reuse)"),
    ("scope", "source data explicit; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem chainTreeCor312Rows_length : chainTreeCor312Rows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ChainTreeCor312Actual

end
