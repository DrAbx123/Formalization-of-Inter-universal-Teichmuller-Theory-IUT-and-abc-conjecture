import tmp.sheaf.xif.paper.S2717Cor312FullTargetActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1E5S2717ConsumerActual — E-5.s2717 consumer aliases

DAG node: e-deep:E5.s2717.  Re-exports the exact equivalence between the single
analytic endpoint S2717UpperGap and the full paper 3.12 target PaperCor312Full, plus
the two projection directions.  No new mathematical content; no closure claim;
gate NOT PASSED.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1E5S2717ConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual

/-- Rows: S2717 consumer status. -/
def e5S2717Rows : List (String × String × String) :=
  [ ("full -> upper gap", "S2717_hupper_of_full_consumer", "PROVED (re-export)"),
    ("upper gap -> full", "S2717_full_of_hupper_consumer", "PROVED (re-export)"),
    ("equivalence", "S2717_full_iff_hupper_consumer", "PROVED (re-export)"),
    ("scope", "S2717UpperGap remains named; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem e5S2717Rows_length : e5S2717Rows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1E5S2717ConsumerActual

end
