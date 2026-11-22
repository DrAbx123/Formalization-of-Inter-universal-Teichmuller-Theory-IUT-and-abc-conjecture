namespace LeanFormal.IUT.XiFPaper.Node09ABCInhabitantScanActual

/-- Exhaustive scan (2026-11-15): no inhabitant/construction of ABCConjecture or
ABCFrontier exists in the tree.  Documentation only. -/
def Node09ABCInhabitantScan : List (String × String) :=
  [ ("verification/abc_with_sorry.lean", "theorem abc_conjecture_with_sorry : ABCConjecture := by sorry; depends on sorryAx, invalid as evidence"),
    ("verification/abc_without_sorry.lean", "theorem abc_conjecture_no_sorry : ABCConjecture := by intro epsilon hepsilon; intentionally incomplete and expected to fail; outside the LeanFormal library"),
    ("LeanFormal/IUT/ABCBridge/UnprovedTarget.lean", "records ABC.proof-target as an Audit.Obligation with status pending; explicitly does not manufacture a theorem"),
    ("LeanFormal/IUT/ABCBridge/Statement.lean", "defines ABCConjecture and its elementary relation abcInequality_is_explicit; no proof of ABCConjecture"),
    ("LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCCards.lean", "chain cards and target-shape equivalence only; module states nothing here proves the chain or any ABC estimate"),
    ("LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean", "cor312ToABCBridge_abcConjecture is conditional on a Cor312ToABCBridgeInterface inhabitant; cor312ToABCBridgeInterface_nonempty_of_abcConjecture constructs from ABCConjecture; nonempty iff ABCConjecture"),
    ("LeanFormal/IUT/ABCBridge/Bridge/ABCFrontier.lean", "abcConjecture_of_frontier is conditional; abcFrontier_iff_abcConjecture states ABCFrontier.{0} iff ABCConjecture; no inhabitant"),
    ("LeanFormal/IUT/ABCBridge/Bridge/ABCFrontierReductions.lean / ABCFrontierSingletonReduction.lean / Cor312PointwiseMembershipWeakening.lean", "all are reductions of witness families to ABCFrontier or ABCConjecture, taking the family as a hypothesis; no construction"),
    ("tmp/local-cft-port, tmp/external, tmp/ported", "no occurrence of ABCConjecture or an ABCFrontier construction"),
    ("metadata-probes/core-construction-map-20261014/actual_stepxi_abc_boundaryaudit.lean", "audit probe with #check/#print axioms only; no construction"),
    ("LeanFormal/IUT/ABCBridge/Bridge/FreyOddConductorHeightCriterion.lean / ABCEllipticHeightCriterion.lean / Arithmetic/LogarithmicBoundEquivalence.lean / ABCHeightArithmeticWeightComparison.lean", "conditional criteria/equivalences/reductions; no unconditional ABC proof") ]

/-- Exact conclusion of the exhaustiveness scan. -/
def Node09ABCInhabitantScanConclusion : List String :=
  [ "no inhabitant or construction of ABCConjecture exists outside verification/abc_with_sorry.lean (which uses sorry) and the intentionally incomplete verification/abc_without_sorry.lean",
    "no inhabitant of ABCFrontier exists; ABCFrontier.{0} is equivalent to ABCConjecture, and every derivation of ABCConjecture from it takes the frontier as a hypothesis",
    "no inhabitant of Cor312ToABCBridgeInterface exists except by assuming ABCConjecture; Nonempty Cor312ToABCBridgeInterface is equivalent to ABCConjecture",
    "therefore there is no unconditional route to ABCConjecture/ABCFrontier in the current tree; the exact paper-level inputs (SNamed/frozen gap2 and actual-p hweightDictionary for the Node09 cards chain) remain necessary",
    "no fake and no new axiom" ]

end LeanFormal.IUT.XiFPaper.Node09ABCInhabitantScanActual
