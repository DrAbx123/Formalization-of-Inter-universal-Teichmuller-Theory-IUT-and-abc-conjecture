import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions
import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierSingletonReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312PointwiseMembershipWeakening
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G3RouteConsumerActual — G3 frontier route consumers (gap / V2 / weakened)

DAG nodes: iutiv-abc:G3, iutiv-abc:G3.single, route alternatives.  Re-exports the exact
route implications and the refutation of the pointwise-reduced premise:

* ABCFrontierGapReduced -> ABCConjecture;
* ABCFrontierGapReducedV2 -> ABCConjecture;
* ABCFrontierPointwiseWeakened -> ABCConjecture;
* not_ABCFrontierPointwiseReduced (the pointwise-reduced premise is empty).

All conditional; no frontier clause is proved.  No closure claim; gate NOT PASSED.
Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G3RouteConsumerActual

open LeanFormal.IUT

/-- Gap-reduced frontier route to ABC. -/
theorem abcConjecture_of_gapReduced (h : ABCFrontierGapReduced.{0}) : ABCConjecture :=
  abcConjecture_of_frontierGapReduced h

/-- F4b-refined gap-reduced frontier route to ABC. -/
theorem abcConjecture_of_gapReducedV2 (h : ABCFrontierGapReducedV2.{0}) : ABCConjecture :=
  abcConjecture_of_frontierGapReducedV2 h

/-- Repaired pointwise-weakened frontier route to ABC. -/
theorem abcConjecture_of_pointwiseWeakened (h : ABCFrontierPointwiseWeakened.{0}) :
    ABCConjecture :=
  abcConjecture_of_frontierPointwiseWeakened h

/-- The pointwise-reduced premise is empty (refuted route; kept for honesty). -/
theorem pointwiseReduced_refuted : ¬ ABCFrontierPointwiseReduced.{0} :=
  not_ABCFrontierPointwiseReduced

/-- Rows: G3 route consumer status. -/
def g3RouteRows : List (String × String × String) :=
  [ ("gapReduced route", "ABCFrontierGapReduced -> ABCConjecture", "PROVED (conditional)"),
    ("gapReducedV2 route", "ABCFrontierGapReducedV2 -> ABCConjecture", "PROVED (conditional)"),
    ("pointwiseWeakened route", "ABCFrontierPointwiseWeakened -> ABCConjecture", "PROVED (conditional)"),
    ("pointwiseReduced route", "not_ABCFrontierPointwiseReduced", "REFUTED (premise empty)"),
    ("scope", "no frontier clause proved; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem g3RouteRows_length : g3RouteRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G3RouteConsumerActual

end
