/-! # Mzk1Stage4CanonicalInterfaceIndexActual (stage4 lane; unique filename)

A601 module: stage4-lane index of the canonical (mainline-owned) ABC two-estimates /
strict-chain interfaces and the stage4-prefixed wrappers that back them (bookkeeping).
No new mathematics.  Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4CanonicalInterfaceIndexActual

/-- Mapping from the canonical (mainline) interface names to stage4 wrapper files. -/
def canonicalInterfaceMap : List (String × String) :=
  [ ("Mzk1ABCTwoEstimatesReductionInterfaceActual",
      "tmp/sheaf/xif/paper/Mzk1Stage4TwoEstimatesReductionActual.lean")
  , ("Mzk1StrictChainSummaryActual",
      "tmp/sheaf/xif/paper/Mzk1Stage4StrictChainSummaryActual.lean")
  , ("Mzk1ABCTwoEstimatesNumericEvidenceActual",
      "tmp/sheaf/xif/paper/Mzk1Stage4ABCTwoEstimatesEvidenceActual.lean")
  , ("Mzk1HqnegHullModelActual (hull-exclusive)",
      "(not written by stage4)")
  , ("Mzk1Cor312HqnegDischargedActual (mainline-exclusive)",
      "(not written by stage4)")
  ]

/-- The interface map has five entries. -/
theorem canonicalInterfaceMap_length : canonicalInterfaceMap.length = 5 := rfl

/-- Every canonical map entry is a pair of strings. -/
theorem canonicalInterfaceMap_wellformed :
    ∀ p ∈ canonicalInterfaceMap, p.1 ≠ "" ∧ p.2 ≠ "" :=
  by
  intro p hp
  simp [canonicalInterfaceMap] at hp
  rcases hp with h | h | h | h | h <;> subst h <;> decide

#check canonicalInterfaceMap
#check canonicalInterfaceMap_length
#check canonicalInterfaceMap_wellformed

end LeanFormal.IUT.XiFPaper.Mzk1Stage4CanonicalInterfaceIndexActual
