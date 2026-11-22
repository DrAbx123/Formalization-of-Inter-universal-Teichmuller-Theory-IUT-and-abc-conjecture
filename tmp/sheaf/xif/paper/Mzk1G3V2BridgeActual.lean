import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierSingletonReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G3V2BridgeActual — G3: GapReducedV2 -> bridge interface -> ABC

DAG nodes: iutiv-abc:G3.single / iutiv-abc:G2.  Exposes the composed route from
the F4b-refined gap frontier to the bridge interface and to ABC.  Conditional on
the frontier clauses; no clause proved.  No closure; gate NOT PASSED.
Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G3V2BridgeActual

open LeanFormal.IUT

universe u

/-- GapReducedV2 -> bridge interface (composed route). -/
def bridgeInterface_of_gapReducedV2 (h : ABCFrontierGapReducedV2.{u}) :
    Cor312ToABCBridgeInterface.{u} :=
  bridgeInterface_of_frontierGapReducedV2 h

/-- GapReducedV2 -> ABC (via the bridge interface). -/
theorem abcConjecture_of_gapReducedV2_bridge (h : ABCFrontierGapReducedV2.{u}) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture (bridgeInterface_of_gapReducedV2 h)

/-- Rows: route status. -/
def g3V2BridgeRows : List (String × String × String) :=
  [ ("GapReducedV2 -> bridge interface", "bridgeInterface_of_gapReducedV2", "PROVED (conditional)"),
    ("GapReducedV2 -> ABC via bridge", "abcConjecture_of_gapReducedV2_bridge", "PROVED (conditional)"),
    ("scope", "frontier clauses named; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem g3V2BridgeRows_length : g3V2BridgeRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G3V2BridgeActual

end
