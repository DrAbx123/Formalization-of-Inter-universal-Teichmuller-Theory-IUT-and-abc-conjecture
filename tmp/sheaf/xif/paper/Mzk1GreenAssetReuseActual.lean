import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.Mzk1F0StepGeometryActual

/-! # Mzk1GreenAssetReuseActual — reuse record of EXIT0 measure/f0 assets

A475: reuses the green assets Mzk1NestedInductionActual (finite measure, well-founded lex
induction) and Mzk1F0StepGeometryActual (f0 map, critical values, degree bounds).  This file
records the existing declarations by name (no theory copying, no assertion of missing P1
strict counting).  No sorry/axiom.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1GreenAssetReuseActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual

attribute [local instance] Classical.decEq

universe u

/-- Row record: EXIT0 assets reused by the C-area chain. -/
def greenAssetReuseRows : List (String × String) :=
  [ ("finite measure", "Mzk1NestedInductionActual: maxDeg/numMax/maxDeg_stepSet_le/numMax_stepSet_lt"),
    ("well-founded lex induction", "Mzk1NestedInductionActual: induction_with_invariant/nested_induction_terminates"),
    ("f0 geometry", "Mzk1F0StepGeometryActual: f0Map/f0Map_infty/f0Map_finite"),
    ("critical values", "Mzk1F0StepGeometryActual: f0CritValue_deg_lt/f0CritValue_deg_le"),
    ("P1 strict numMax", "repo-current missing (A475 evidence)") ]

theorem greenAssetReuseRows_length : greenAssetReuseRows.length = 5 := rfl

#check maxDeg_stepSet_le
#check numMax_stepSet_lt
#check induction_with_invariant
#check nested_induction_terminates
#check f0Map_infty
#check f0Map_finite
#check f0CritValue_deg_lt

end LeanFormal.IUT.XiFPaper.Mzk1GreenAssetReuseActual
end
