import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G3FrontierEquivActual — G3: ABCFrontier is equivalent strength to ABC

DAG node: iutiv-abc:G3 (frontier).  Exposes abcFrontier_iff_abcConjecture and the
real-line variant, recording that ABCFrontier and ABCFrontierRealLine are NOT cheap
shortcuts (each is equivalent to ABC).  No new mathematical content; no closure.
GATE NOT PASSED; registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G3FrontierEquivActual

open LeanFormal.IUT

/-- ABCFrontier is equivalent to ABC. -/
theorem abcFrontier_iff_abcConjecture_consumer :
    ABCFrontier.{0} ↔ ABCConjecture :=
  abcFrontier_iff_abcConjecture

/-- The real-line frontier is equivalent to ABC. -/
theorem abcFrontierRealLine_iff_abcConjecture_consumer :
    ABCFrontierRealLine ↔ ABCConjecture :=
  abcFrontierRealLine_iff_abcConjecture

/-- Frontier -> ABC and ABC -> frontier directions. -/
theorem abcConjecture_of_abcFrontier (h : ABCFrontier.{0}) : ABCConjecture :=
  abcFrontier_iff_abcConjecture_consumer.mp h

theorem abcFrontier_of_abcConjecture (h : ABCConjecture) : ABCFrontier.{0} :=
  abcFrontier_iff_abcConjecture_consumer.mpr h

/-- Rows: frontier strength status. -/
def g3FrontierEquivRows : List (String × String × String) :=
  [ ("frontier <-> ABC", "abcFrontier_iff_abcConjecture_consumer", "PROVED equivalence"),
    ("real-line frontier <-> ABC", "abcFrontierRealLine_iff_abcConjecture_consumer", "PROVED equivalence"),
    ("direction consumers", "abcConjecture_of_abcFrontier / abcFrontier_of_abcConjecture", "PROVED"),
    ("warning", "frontier is not a cheap shortcut (equivalent strength)", "INTEGRITY") ]

theorem g3FrontierEquivRows_length : g3FrontierEquivRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G3FrontierEquivActual

end
