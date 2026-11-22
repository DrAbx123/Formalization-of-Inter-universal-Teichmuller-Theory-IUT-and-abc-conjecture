import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G2FrontierActual — G2/G3 consumer: frontier -> bridge interface -> ABC

DAG nodes: iutiv-abc:G2 / iutiv-abc:G3 (bridge routes).  Re-exports the exact
route from ABCFrontier to Cor312ToABCBridgeInterface (bridgeInterface_of_frontier)
and the composed ABC consequence.  Conditional on the frontier clauses.
No closure claim; gate NOT PASSED.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G2FrontierActual

open LeanFormal.IUT

universe u

/-- Frontier -> bridge interface (composed route). -/
def bridgeInterface_of_frontierRoute (h : ABCFrontier.{u}) :
    Cor312ToABCBridgeInterface.{u} :=
  bridgeInterface_of_frontier h

/-- Frontier -> ABC (via the bridge interface, composed). -/
theorem abcConjecture_of_frontierRoute (h : ABCFrontier.{u}) : ABCConjecture :=
  cor312ToABCBridge_abcConjecture (bridgeInterface_of_frontierRoute h)

/-- Frontier -> ABC directly (existing route; re-export for fragment consumers). -/
theorem abcConjecture_of_frontier_direct (h : ABCFrontier.{u}) : ABCConjecture :=
  abcConjecture_of_frontier h

/-- Rows: G2/G3 frontier route consumer status. -/
def g2FrontierRows : List (String × String × String) :=
  [ ("frontier -> bridge interface", "bridgeInterface_of_frontierRoute", "PROVED (conditional)"),
    ("frontier -> ABC via bridge", "abcConjecture_of_frontierRoute", "PROVED (conditional)"),
    ("frontier -> ABC direct", "abcConjecture_of_frontier_direct", "PROVED (conditional)"),
    ("scope", "frontier clauses NAMED; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem g2FrontierRows_length : g2FrontierRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G2FrontierActual

end
