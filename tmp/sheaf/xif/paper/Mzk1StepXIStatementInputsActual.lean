import tmp.sheaf.xif.paper.Mzk1DeepStatementLayerV2Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1StepXIStatementInputsActual — StepXI prerequisite statements (clean, no True placeholder)

Replaces the True-placeholder StepXI input label file by actual statement-layer
structures from Mzk1DeepStatementLayerV2Actual.  This is a statement bundle for
StepXI inputs; no closure; gate NOT PASSED.  Registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIStatementInputsActual

open LeanFormal.IUT.XiFPaper.Mzk1DeepStatementLayerV2Actual

/-- The prerequisite statements consumed by the StepXI construction. -/
structure StepXIStatementInputs where
  sec1sec2 : Sec1ToSec2GapStatement
  trans : IUTIVSec2ArithmeticTransitionStatement
  t110 : IUTIVThm110ActualStatement
  pnt : IUTIVProp22PNTStatement
  heightInput : HeightInputStatement
  undilatedInput : UndilatedInputStatement
  gapSupply : Cor312GapSupplyData
  hcor312 : HCor312Statement
  hslack : HSlackStatement

theorem stepXIInputs_sec1sec2 (I : StepXIStatementInputs) :
    I.sec1sec2.display_to_comparison :=
  sec1_sec2_transfer I.sec1sec2

theorem stepXIInputs_transition (I : StepXIStatementInputs) :
    I.trans.arithmetic_transition :=
  sec2_transition I.trans

theorem stepXIInputs_thm110actual (I : StepXIStatementInputs) :
    I.t110.logVolume_estimate :=
  thm110_actual I.t110

theorem stepXIInputs_height (I : StepXIStatementInputs) :
    I.heightInput.uniform_valuation_bound :=
  height_uniform I.heightInput

theorem stepXIInputs_undilated (I : StepXIStatementInputs) :
    I.undilatedInput.undilated_region_volume :=
  undilated_bound I.undilatedInput

def stepXIStatementInputsRows : List (String × String × String) :=
  [ ("statement bundle", "StepXIStatementInputs", "DEF (reuses deep layer)"),
    ("projections", "stepXIInputs_sec1sec2/transition/thm110actual/height/undilated", "PROVED"),
    ("replaces", "True-placeholder StepXIInput file", "SUPERSEDED (not imported)"),
    ("scope", "statements only; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem stepXIStatementInputsRows_length : stepXIStatementInputsRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1StepXIStatementInputsActual

end
