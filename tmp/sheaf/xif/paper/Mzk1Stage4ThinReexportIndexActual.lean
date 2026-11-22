import tmp.sheaf.xif.paper.Mzk1Stage4A618ObstructionConsumerActual
import tmp.sheaf.xif.paper.Mzk1Stage4FinalConsumerWrapupActual

/-! # Mzk1Stage4ThinReexportIndexActual (stage4 lane; thin re-export index)

A645 module: thin re-export index — the canonical GREEN A618 obstruction and the stage4
consumer wrappers, plus axiom prints for the re-exported consumers.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ThinReexportIndexActual

/-- Mapping from retired/other-lane sources to the canonical green source used. -/
def reexportMap : List (String × String) :=
  [ ("Mzk1A618MachineProofActual.concreteS1902Interface_insufficient (RETIRED)",
      "Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction")
  , ("Mzk1Stage4A618MachineConsumerActual (thin re-export)",
      "Mzk1Stage4A618ObstructionConsumerActual")
  ]

/-- The re-export map has two entries. -/
theorem reexportMap_length : reexportMap.length = 2 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4A618ObstructionConsumerActual.stage4_identity_obstruction
#print axioms Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4GapStructuralConsumerActual.gapStructuralConsumer_height

#check LeanFormal.IUT.XiFPaper.Mzk1Stage4A618ObstructionConsumerActual.stage4_identity_obstruction
#check LeanFormal.IUT.XiFPaper.Mzk1Stage4FinalConsumerWrapupActual.wrapup_gap_height

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ThinReexportIndexActual
end
