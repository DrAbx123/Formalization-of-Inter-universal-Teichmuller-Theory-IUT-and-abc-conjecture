import tmp.sheaf.xif.paper.ShehddABCFrontierFormEquivalencesActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1FrontierFormEquivConsumerActual — ABC frontier form-equivalence consumers

Reuses the EXIT0 Shehdd frontier form equivalences: ABCFrontier is equivalent to
both the log form and the additive height-weight form, and yields each.  These are
form equivalences only; the frontier itself remains unproved.  No closure; gate NOT
PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FrontierFormEquivConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.ShehddABCFrontierFormEquivalencesActual

theorem frontier_iff_log_consumer :
    ABCFrontier.{0} ↔ ABCLogConjecture :=
  abcFrontier_iff_abcLogConjecture

theorem frontier_iff_additive_consumer :
    ABCFrontier.{0} ↔ ABCHeightWeightAdditiveBoundV2 :=
  abcFrontier_iff_abcHeightWeightAdditive

theorem log_of_frontier_consumer (h : ABCFrontier.{0}) : ABCLogConjecture :=
  abcLogConjecture_of_frontier h

theorem additive_of_frontier_consumer (h : ABCFrontier.{0}) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcHeightWeightAdditive_of_frontier h

def frontierFormConsumerRows : List (String × String × String) :=
  [ ("frontier <-> log", "frontier_iff_log_consumer", "PROVED (reuse)"),
    ("frontier <-> additive", "frontier_iff_additive_consumer", "PROVED (reuse)"),
    ("directions", "log_of_frontier_consumer / additive_of_frontier_consumer", "PROVED (reuse)"),
    ("scope", "frontier unproved; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem frontierFormConsumerRows_length : frontierFormConsumerRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1FrontierFormEquivConsumerActual

end
