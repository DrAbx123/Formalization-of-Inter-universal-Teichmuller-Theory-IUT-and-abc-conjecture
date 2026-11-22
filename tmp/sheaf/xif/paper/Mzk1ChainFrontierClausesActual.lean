import LeanFormal/IUT/ABCBridge/Bridge/ABCFrontierReductions

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ChainFrontierClausesActual — A475 chained adapters: ABC frontier clauses

Reuses the clause definitions and reduction slots already in
`ABCFrontierReductions.lean:77/102/119/136/157/177/199/221/232/243/256/273/294/301/307`
and chains them: gap-reduced/pointwise-reduced frontier -> ABCFrontier ->
Cor312ToABCBridgeInterface -> ABCConjecture. No theory duplication, no axioms;
no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainFrontierClausesActual

open LeanFormal.IUT

/-- Reuse bundle of the frontier clause definitions (single term). -/
def chain_frontier_clauses :=
  (FrontierHeightWeightClause,
   FrontierWeightRegionClause,
   FrontierUnitNormalizationClause,
   FrontierSplitClause,
   FrontierPointFinitenessClause,
   FrontierPointVolumeWeightClause,
   FrontierUnitMembershipClause,
   FrontierPointHeightClause,
   ABCFrontierGapReduced,
   ABCFrontierPointwiseReduced)

/-- Gap-reduced frontier -> ABCFrontier (donor slot). -/
theorem chain_gapReduced_to_frontier (h : ABCFrontierGapReduced.{0}) : ABCFrontier.{0} :=
  ABCFrontier.reduce_gapReductionInputs h

/-- Pointwise-reduced frontier -> ABCFrontier (donor slot). -/
theorem chain_pointwise_to_frontier (h : ABCFrontierPointwiseReduced.{0}) : ABCFrontier.{0} :=
  ABCFrontier.reduce_pointwiseResidual h

/-- Gap-reduced frontier -> bridge interface (donor slot). -/
def chain_bridge_of_gapReduced (h : ABCFrontierGapReduced.{0}) :
    Cor312ToABCBridgeInterface.{0} :=
  bridgeInterface_of_frontierGapReduced h

/-- Pointwise-reduced frontier -> bridge interface (donor slot). -/
def chain_bridge_of_pointwise (h : ABCFrontierPointwiseReduced.{0}) :
    Cor312ToABCBridgeInterface.{0} :=
  bridgeInterface_of_frontierPointwiseReduced h

/-- Gap-reduced frontier -> ABCConjecture (two-donor chain). -/
theorem chain_gapReduced_abc (h : ABCFrontierGapReduced.{0}) : ABCConjecture :=
  abcConjecture_of_frontierGapReduced h

/-- Pointwise-reduced frontier -> ABCConjecture (two-donor chain). -/
theorem chain_pointwise_abc (h : ABCFrontierPointwiseReduced.{0}) : ABCConjecture :=
  abcConjecture_of_frontierPointwiseReduced h

/-- Real-line frontier -> ABCConjecture (reduce_realLine + abcConjecture_of_frontier). -/
theorem chain_realLine_abc (h : ABCFrontierRealLine) : ABCConjecture :=
  abcConjecture_of_frontier (ABCFrontier.reduce_realLine h)

def chainFrontierRows : List (String × String × String) :=
  [ ("frontier clauses bundle", "REUSED donor defs", "chain_frontier_clauses"),
    ("gapReduced -> ABCFrontier", "CHAIN PROVED", "chain_gapReduced_to_frontier"),
    ("pointwise -> ABCFrontier", "CHAIN PROVED", "chain_pointwise_to_frontier"),
    ("gapReduced -> bridge interface", "REUSED donor", "chain_bridge_of_gapReduced"),
    ("pointwise -> bridge interface", "REUSED donor", "chain_bridge_of_pointwise"),
    ("gapReduced -> ABC", "CHAIN PROVED", "chain_gapReduced_abc"),
    ("pointwise -> ABC", "CHAIN PROVED", "chain_pointwise_abc"),
    ("realLine -> ABC", "CHAIN PROVED", "chain_realLine_abc") ]

theorem chainFrontierRows_length : chainFrontierRows.length = 8 := rfl

#check chain_gapReduced_abc
#check chainFrontierRows_length

end LeanFormal.IUT.XiFPaper.Mzk1ChainFrontierClausesActual
end