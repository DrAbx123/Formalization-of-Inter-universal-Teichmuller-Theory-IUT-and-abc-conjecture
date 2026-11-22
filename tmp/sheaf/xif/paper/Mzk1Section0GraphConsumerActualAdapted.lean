import tmp.sheaf.xif.paper.Mzk1Section0GraphActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1Section0GraphConsumerActualAdapted (adapted copy, A475 reuse) — Section-0 graph reachability consumers

Reuses the EXIT0 Section-0 graph facts (successor edge, reachability) to expose
monotonicity consumers.  No new math; no closure; gate NOT PASSED; registry 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0GraphConsumerActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1Section0GraphActual

theorem succEdge_le_consumer {n m : ℤ} (h : SuccEdge n m) : n ≤ m :=
  succEdge_le h

theorem reach_le_consumer {n m : ℤ} (h : Reach n m) : n ≤ m :=
  reach_le h

def section0GraphConsumerRows : List (String × String × String) :=
  [ ("successor edge monotone", "succEdge_le_consumer", "PROVED (reuse)"),
    ("reachability monotone", "reach_le_consumer", "PROVED (reuse)"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem section0GraphConsumerRows_length : section0GraphConsumerRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Section0GraphConsumerActualAdapted

end
