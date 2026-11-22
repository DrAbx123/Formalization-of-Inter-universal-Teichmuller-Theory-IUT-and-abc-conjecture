import tmp.sheaf.xif.paper.S2717Cor312FullTargetActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1E5S2717ConsumerActualV2 — E-5.s2717 consumer aliases

DAG node: e-deep:E5.s2717.  Re-exports the full-target/upper-gap equivalence as
defs.  S2717UpperGap remains named; no closure; gate NOT PASSED.
Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1E5S2717ConsumerActualV2

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual

/-- Full paper 3.12 target -> unique upper gap. -/
def S2717_hupper_of_full_consumer := S2717_hupper_of_full

/-- Unique upper gap -> full paper 3.12 target. -/
def S2717_full_of_hupper_consumer := S2717_full_of_hupper

/-- Exact equivalence of the full target and the unique upper gap. -/
def S2717_full_iff_hupper_consumer := S2717_full_iff_hupper

/-- Rows. -/
def e5S2717RowsV2 : List (String × String × String) :=
  [ ("full <-> upper gap", "S2717_full_iff_hupper_consumer", "PROVED equivalence (def alias)"),
    ("directions", "S2717_hupper_of_full_consumer / S2717_full_of_hupper_consumer", "DEF aliases"),
    ("scope", "S2717UpperGap named; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem e5S2717RowsV2_length : e5S2717RowsV2.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1E5S2717ConsumerActualV2

end
