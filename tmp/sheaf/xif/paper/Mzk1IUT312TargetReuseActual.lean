import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier

/-!
# Mzk1IUT312TargetReuseActual — IUT 3.12 target statement node linked to EXISTING repo
assets (Lead A475 reuse rule)

Existing assets reused (all with oleans):
* LeanFormal/IUT/ABCBridge/Statement.lean (radical/ABCInequality/ABCConjecture);
* LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean
  (Cor312EpsilonArithmeticComparison, Cor312ToABCBridgeInterface,
  cor312ToABCBridge_heightBound);
* LeanFormal/IUT/ABCBridge/Bridge/ABCFrontier.lean (ABCFrontier and the
  abcConjecture_of_frontier / abcFrontier_iff_abcConjecture reductions).

This file only re-exports and rows the target-statement linkage for
iut-pre-abc:IUT312.statement / Gap.iut312TopStatement and the DAG T0/T1/T3 nodes; the target
sentence itself remains the paper statement (no new axiom/sorry, no closure claim).
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1IUT312TargetReuseActual

open LeanFormal.IUT

/-- The T0 target statement (existing tree declaration). -/
def abcTargetReuse :=
  @ABCConjecture

/-- The explicit ABC inequality statement (existing tree declaration). -/
def abcInequalityReuse :=
  @ABCInequality

/-- The Cor 3.12 -> ABC bridge height-bound (existing tree declaration). -/
def cor312BridgeHeightBoundReuse :=
  @cor312ToABCBridge_heightBound

/-- The ABC frontier reduction: abc conjecture from frontier (existing declaration). -/
def abcConjectureOfFrontierReuse :=
  @abcConjecture_of_frontier

/-- The frontier <=> abc conjecture equivalence (existing declaration). -/
def abcFrontierIffReuse :=
  @abcFrontier_iff_abcConjecture

/-- Target-reuse rows: (target DAG node, existing asset, status). -/
def iut312TargetReuseRows : List (String × String × String) :=
  [ ("iut-pre-abc:IUT312.statement / T0-abc-target", "ABCBridge/Statement.ABCConjecture (tree olean)", "REUSE (paper target statement)"),
    ("T1-cor312-abc-bridge", "Cor312ToABCBridgeInterface.cor312ToABCBridge_heightBound", "REUSE (tree olean)"),
    ("T3-abc-frontier", "ABCFrontier.abcConjecture_of_frontier / abcFrontier_iff_abcConjecture", "REUSE (tree olean)"),
    ("Gap.iut312TopStatement", "ABCBridge/Statement.ABCConjecture + bridge interface (paper-level assembly)", "NAMED (assembly)"),
    ("IUT III Cor 3.12 input", "Cor312EpsilonArithmeticComparison (bridge interface)", "REUSE (tree olean)") ]

/-- The target-reuse row record has five rows. -/
theorem iut312TargetReuseRows_length : iut312TargetReuseRows.length = 5 := rfl

#check abcTargetReuse
#check abcInequalityReuse
#check cor312BridgeHeightBoundReuse
#check abcConjectureOfFrontierReuse
#check abcFrontierIffReuse
#check iut312TargetReuseRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUT312TargetReuseActual
end
