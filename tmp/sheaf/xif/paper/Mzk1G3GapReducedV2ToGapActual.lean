import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierSingletonReduction
import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G3GapReducedV2ToGapActual — route relation: GapReducedV2 => GapReduced

DAG nodes: iutiv-abc:G3.single / iutiv-abc:G3 red.  The F4b-refined frontier
(ABCFrontierGapReducedV2) is stronger than the gap-reduced frontier
(ABCFrontierGapReduced): its singleton-weight/volume and region-finiteness clauses
reassemble the F4b weight-region clause by ABCFrontier.reduce_weightRegionInputs.
This gives the route edge V2 -> gapReduced (conditional; no clause proved).

No closure claim; gate NOT PASSED.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G3GapReducedV2ToGapActual

open LeanFormal.IUT

universe u

/-- The refined gap frontier implies the gap-reduced frontier. -/
theorem gapReduced_of_gapReducedV2 (h : ABCFrontierGapReducedV2.{u}) :
    ABCFrontierGapReduced.{u} := by
  obtain ⟨X, W, point, hhw, hsingle, hfin, hunit, hsplit, hptfin, hpoint⟩ := h
  exact ⟨X, W, point, hhw,
    ABCFrontier.reduce_weightRegionInputs W point hsingle hfin,
    hunit, hsplit, hptfin, hpoint⟩

/-- Composed route: refined gap frontier -> gap frontier -> ABC. -/
theorem abcConjecture_of_gapReducedV2_via_gap (h : ABCFrontierGapReducedV2.{u}) :
    ABCConjecture :=
  abcConjecture_of_frontierGapReduced (gapReduced_of_gapReducedV2 h)

/-- Rows: route relation. -/
def g3GapRouteRows : List (String × String × String) :=
  [ ("V2 -> gapReduced", "gapReduced_of_gapReducedV2 (reduce_weightRegionInputs)", "PROVED (conditional)"),
    ("V2 -> ABC via gap", "abcConjecture_of_gapReducedV2_via_gap", "PROVED (conditional)"),
    ("scope", "no frontier clause proved; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem g3GapRouteRows_length : g3GapRouteRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G3GapReducedV2ToGapActual

end
