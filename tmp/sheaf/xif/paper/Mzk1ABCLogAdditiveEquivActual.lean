import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ABCLogAdditiveEquivActual — ABC log form <-> additive height-weight bound

DAG nodes: iutiv-abc:G0.log / iutiv-abc:HW.add.  Composes the two proved
equivalences: ABCConjecture <-> ABCLogConjecture and ABCConjecture <->
ABCHeightWeightAdditiveBoundV2, yielding a direct calibration between the log
form and the additive height-weight form (both directions).  No new arithmetic
content; no closure; gate NOT PASSED.  Registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCLogAdditiveEquivActual

open LeanFormal.IUT

/-- ABC log form <-> additive height-weight bound (both directions). -/
theorem abcLogConjecture_iff_additiveBoundV2 :
    ABCLogConjecture ↔ ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_abcLogConjecture.symm.trans
    abcConjecture_iff_ABCHeightWeightAdditiveBoundV2

/-- Log form -> additive form. -/
theorem additiveBoundV2_of_abcLogConjecture (h : ABCLogConjecture) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcLogConjecture_iff_additiveBoundV2.mp h

/-- Additive form -> log form. -/
theorem abcLogConjecture_of_additiveBoundV2 (h : ABCHeightWeightAdditiveBoundV2) :
    ABCLogConjecture :=
  abcLogConjecture_iff_additiveBoundV2.mpr h

/-- Rows: calibration status. -/
def abcLogAdditiveRows : List (String × String × String) :=
  [ ("log <-> additive", "abcLogConjecture_iff_additiveBoundV2", "PROVED equivalence"),
    ("directions", "additiveBoundV2_of_abcLogConjecture / abcLogConjecture_of_additiveBoundV2", "PROVED"),
    ("scope", "no new arithmetic; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem abcLogAdditiveRows_length : abcLogAdditiveRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCLogAdditiveEquivActual

end
