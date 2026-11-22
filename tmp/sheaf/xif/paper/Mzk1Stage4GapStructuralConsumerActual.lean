import tmp.sheaf.xif.paper.Mzk1Stage4GapConsumerChainActual

/-! # Mzk1Stage4GapStructuralConsumerActual (stage4 lane; Gap structural consumer)

A639 module (Gap1/Gap2 progress): structural consumer record assembling the numeric gap
instances, the region-volume bound, and the transitive height bound, with axiom prints.
No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GapStructuralConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightEstimateActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4GapInstancesNumericActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4GapConsumerChainActual

/-- The structural gap consumer record. -/
structure GapStructuralConsumer where
  /-- Gap 1 structure. -/
  gap1 : Gap1 height11 regionVol11
  /-- Gap 2 structure. -/
  gap2 : Gap2 regionVol11 (Real.log 11) 11 0 (1 / 10)
  /-- the transitive height bound. -/
  height_bound : height11 ≤ (1 + 1 / 10 : Real) * Real.log 11 + (11 + 0)

/-- Construct the structural gap consumer. -/
noncomputable def gapStructuralConsumer : GapStructuralConsumer where
  gap1 := gap1_instance_height
  gap2 := gap2_instance_region
  height_bound := height_le_weight_transitive

/-- Consumer: the recorded height bound. -/
theorem gapStructuralConsumer_height :
    height11 ≤ (1 + 1 / 10 : Real) * Real.log 11 + (11 + 0) :=
  gapStructuralConsumer.height_bound

#print axioms gapStructuralConsumer_height
#print axioms height_le_weight_transitive

#check GapStructuralConsumer
#check gapStructuralConsumer
#check gapStructuralConsumer_height

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GapStructuralConsumerActual
end
