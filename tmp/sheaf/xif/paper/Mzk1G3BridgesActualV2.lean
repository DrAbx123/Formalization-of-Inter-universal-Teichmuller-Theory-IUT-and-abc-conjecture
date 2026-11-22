import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions
import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierSingletonReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G3BridgesActualV2 — G3 bridge routes (gapReduced / gapReducedV2 -> interface -> ABC)

DAG nodes: iutiv-abc:G3 / iutiv-abc:G2.  The two frontier bridge constructions return
data (Cor312ToABCBridgeInterface), so they are defs, not theorems.  Both premises are
refuted by ABCFrontierHeightWeightRefutation (not_ABCFrontierGapReduced /
not_ABCFrontierGapReducedV2); the composed implications are therefore valid but
unusable, recorded as GAP/REFUTED in the fragment.
No closure claim; gate NOT PASSED.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G3BridgesActualV2

open LeanFormal.IUT

universe u

/-- GapReduced -> bridge interface (def, data). -/
def bridgeInterface_of_gapReduced (h : ABCFrontierGapReduced.{u}) :
    Cor312ToABCBridgeInterface.{u} :=
  bridgeInterface_of_frontierGapReduced h

/-- GapReducedV2 -> bridge interface (def, data). -/
def bridgeInterface_of_gapReducedV2 (h : ABCFrontierGapReducedV2.{u}) :
    Cor312ToABCBridgeInterface.{u} :=
  bridgeInterface_of_frontierGapReducedV2 h

/-- GapReduced -> ABC via bridge (conditional implication). -/
theorem abcConjecture_of_gapReduced_bridge (h : ABCFrontierGapReduced.{u}) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture (bridgeInterface_of_gapReduced h)

/-- GapReducedV2 -> ABC via bridge (conditional implication). -/
theorem abcConjecture_of_gapReducedV2_bridge (h : ABCFrontierGapReducedV2.{u}) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture (bridgeInterface_of_gapReducedV2 h)

/-- Rows: route status. -/
def g3BridgesRows : List (String × String × String) :=
  [ ("gapReduced -> bridge", "bridgeInterface_of_gapReduced", "DEF (premise refuted)"),
    ("gapReducedV2 -> bridge", "bridgeInterface_of_gapReducedV2", "DEF (premise refuted)"),
    ("gapReduced -> ABC", "abcConjecture_of_gapReduced_bridge", "PROVED implication (premise refuted)"),
    ("gapReducedV2 -> ABC", "abcConjecture_of_gapReducedV2_bridge", "PROVED implication (premise refuted)"),
    ("scope", "routes unusable; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem g3BridgesRows_length : g3BridgesRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G3BridgesActualV2

end
