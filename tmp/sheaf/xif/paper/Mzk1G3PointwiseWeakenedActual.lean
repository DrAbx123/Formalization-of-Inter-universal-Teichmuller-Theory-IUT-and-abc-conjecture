import LeanFormal.IUT.ABCBridge.Bridge.Cor312PointwiseMembershipWeakening
import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierSingletonReduction
import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G3PointwiseWeakenedActual — route relation: pointwise-weakened => gapReduced => ABC

DAG node: iutiv-abc:G3 route alternatives.  The repaired pointwise frontier
(ABCFrontierPointwiseWeakened) lands in the gap-reduced frontier by
pointwiseWeakened_to_gapReduced; this file exposes that route relation and the
composed ABC consequence.  The original pointwise-reduced frontier remains REFUTED
(not_ABCFrontierPointwiseReduced), so the weakened route is the repaired one.

Conditional; no frontier clause proved; no closure; gate NOT PASSED.
Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G3PointwiseWeakenedActual

open LeanFormal.IUT

universe u

/-- The repaired pointwise frontier implies the gap-reduced frontier. -/
theorem gapReduced_of_pointwiseWeakened (h : ABCFrontierPointwiseWeakened.{u}) :
    ABCFrontierGapReduced.{u} :=
  pointwiseWeakened_to_gapReduced h

/-- Composed route: repaired pointwise frontier -> gap frontier -> ABC. -/
theorem abcConjecture_of_pointwiseWeakened_via_gap
    (h : ABCFrontierPointwiseWeakened.{u}) : ABCConjecture :=
  abcConjecture_of_frontierGapReduced (gapReduced_of_pointwiseWeakened h)

/-- The original pointwise-reduced premise is empty (refuted route). -/
theorem pointwiseReduced_empty : ¬ ABCFrontierPointwiseReduced.{u} :=
  not_ABCFrontierPointwiseReduced

/-- Rows: route relation and refutation. -/
def g3PointwiseRows : List (String × String × String) :=
  [ ("pointwiseWeakened -> gapReduced", "gapReduced_of_pointwiseWeakened", "PROVED (conditional)"),
    ("pointwiseWeakened -> ABC via gap", "abcConjecture_of_pointwiseWeakened_via_gap", "PROVED (conditional)"),
    ("pointwiseReduced", "pointwiseReduced_empty (not_ABCFrontierPointwiseReduced)", "REFUTED (premise empty)"),
    ("scope", "no frontier clause proved; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem g3PointwiseRows_length : g3PointwiseRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G3PointwiseWeakenedActual

end
