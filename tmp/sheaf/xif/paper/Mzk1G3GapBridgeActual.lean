import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G3GapBridgeActual — G3: GapReduced -> bridge interface -> ABC

DAG nodes: iutiv-abc:G3 / iutiv-abc:G2.  Exposes the composed route from the
gap-reduced frontier to the bridge interface and ABC.  Conditional on the frontier
clauses; no clause proved.  No closure; gate NOT PASSED.
Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G3GapBridgeActual

open LeanFormal.IUT

universe u

/-- GapReduced -> bridge interface. -/
def bridgeInterface_of_gapReduced (h : ABCFrontierGapReduced.{u}) :
    Cor312ToABCBridgeInterface.{u} :=
  bridgeInterface_of_frontierGapReduced h

/-- GapReduced -> ABC via the bridge interface. -/
theorem abcConjecture_of_gapReduced_bridge (h : ABCFrontierGapReduced.{u}) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture (bridgeInterface_of_gapReduced h)

/-- Rows: route status. -/
def g3GapBridgeRows : List (String × String × String) :=
  [ ("GapReduced -> bridge", "bridgeInterface_of_gapReduced", "PROVED (conditional)"),
    ("GapReduced -> ABC via bridge", "abcConjecture_of_gapReduced_bridge", "PROVED (conditional)"),
    ("scope", "frontier clauses named; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem g3GapBridgeRows_length : g3GapBridgeRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G3GapBridgeActual

end
