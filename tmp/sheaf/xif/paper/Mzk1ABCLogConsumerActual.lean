import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ABCLogConsumerActual — ABC log-equivalence consumers (DAG node mainline:abc-log-equivalence)

Exposes both directions of the proved equivalence between ABCConjecture and
ABCLogConjecture.  This is a consumer file; no new mathematical content.
No closure claim; gate NOT PASSED.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCLogConsumerActual

open LeanFormal.IUT

/-- ABCConjecture -> ABCLogConjecture. -/
theorem abcLogConjecture_of_abcConjecture (h : ABCConjecture) : ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture.mp h

/-- ABCLogConjecture -> ABCConjecture. -/
theorem abcConjecture_of_abcLogConjecture (h : ABCLogConjecture) : ABCConjecture :=
  abcConjecture_iff_abcLogConjecture.mpr h

/-- Rows: log-equivalence consumer status. -/
def abcLogRows : List (String × String × String) :=
  [ ("ABC <-> ABCLog", "abcConjecture_iff_abcLogConjecture (core)", "PROVED equivalence"),
    ("forward/backward", "abcLogConjecture_of_abcConjecture / abcConjecture_of_abcLogConjecture", "PROVED"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem abcLogRows_length : abcLogRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCLogConsumerActual

end
