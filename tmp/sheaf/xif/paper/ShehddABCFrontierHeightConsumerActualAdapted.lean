import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# ShehddABCFrontierHeightConsumerActualAdapted — ABCFrontier => bridge interface / height bound

STEP 0 prior-art (reuse only):
* ABCBridge/Bridge/ABCFrontier.lean: FrontierHeightComparisonClause,
  FrontierRegionComparisonClause, ABCFrontier, bridgeInterface_of_frontier,
  abcConjecture_of_frontier;
* ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean: cor312ToABCBridge_heightBound
  (interface => per-epsilon additive height bound).

This file exposes the frontier's consumer consequences: the bridge interface, the
per-epsilon height bound, and ABC.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddABCFrontierHeightConsumerActualAdapted

open LeanFormal.IUT

universe u

/-- **PROVED consumer:** a frontier witness yields the bridge interface (via the proved
`bridgeInterface_of_frontier`). -/
def frontier_bridgeInterface (h : ABCFrontier.{u}) :
    Cor312ToABCBridgeInterface :=
  bridgeInterface_of_frontier h

/-- **PROVED consumer:** a frontier witness yields the per-epsilon additive height
bound consumed by the ABC comparison chain. -/
theorem frontier_heightBound (h : ABCFrontier.{u}) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ A : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound (bridgeInterface_of_frontier h)

/-- **PROVED consumer:** a frontier witness yields ABC AND its height bound. -/
theorem frontier_abc_and_heightBound (h : ABCFrontier.{u}) :
    ABCConjecture ∧
      (∀ epsilon : ℝ, 0 < epsilon → ∃ A : ℝ,
        ∀ a b c : Nat, IsABCTriple a b c →
          Height.logHeight₁ (abcRationalPoint a c) ≤
            (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) :=
  ⟨abcConjecture_of_frontier h, frontier_heightBound h⟩

/-- Row record: reused frontier assets vs the consumer interface. -/
def frontierHeightRows : List (String × String × String) :=
  [ ("frontier comparison clauses + bridgeInterface_of_frontier", "REUSED DEF/PROVED", "ABCFrontier.lean")
  , ("interface => per-epsilon height bound", "REUSED PROVED", "Cor312ToABCBridgeInterface.cor312ToABCBridge_heightBound")
  , ("frontier => bridge interface consumer", "COMPOSED PROVED", "frontier_bridgeInterface")
  , ("frontier => height bound", "COMPOSED PROVED", "frontier_heightBound")
  , ("frontier => ABC + height bound", "COMPOSED PROVED", "frontier_abc_and_heightBound")
  , ("frontier premise itself (both clauses)", "NAMED (frontier hypothesis)", "carried as hypothesis, not asserted") ]

theorem frontierHeightRows_length : frontierHeightRows.length = 6 := rfl

#check frontier_bridgeInterface
#check frontier_heightBound
#check frontier_abc_and_heightBound
#check frontierHeightRows_length

end LeanFormal.IUT.XiFPaper.ShehddABCFrontierHeightConsumerActualAdapted
end
