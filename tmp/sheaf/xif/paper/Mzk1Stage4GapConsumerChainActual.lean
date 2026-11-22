import tmp.sheaf.xif.paper.Mzk1Stage4GapInstancesNumericActual

/-! # Mzk1Stage4GapConsumerChainActual (stage4 lane; Gap1/Gap2 consumer chain)

A637 module (Gap1/Gap2 progress): consumer chain from the concrete numeric gap
instances — both gap structures, the region-volume bound, and the transitive height
bound via Gap1 then Gap2.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GapConsumerChainActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightEstimateActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4GapInstancesNumericActual

/-- Both numeric gap structures hold for the 11a1 data. -/
theorem gap_instances_chain :
    Gap1 height11 regionVol11 ∧ Gap2 regionVol11 (Real.log 11) 11 0 (1 / 10) :=
  ⟨gap1_instance_height, gap2_instance_region⟩

/-- The region-volume bound from the Gap2 instance. -/
theorem region_le_weight_from_gap2 :
    regionVol11 ≤ (1 + 1 / 10 : Real) * Real.log 11 + 11 + 0 :=
  gap2_instance_region.bound

/-- Transitive height bound: Gap1 gives `height ≤ regionVol`, Gap2 then bounds the
region volume by the epsilon weight. -/
theorem height_le_weight_transitive :
    height11 ≤ (1 + 1 / 10 : Real) * Real.log 11 + (11 + 0) :=
  le_trans gap1_instance_height.bound (by linarith [region_le_weight_from_gap2])

/-- The transitive bound in existential-constant form. -/
theorem height_le_weight_transitive_exists :
    ∃ A : Real, height11 ≤ (1 + 1 / 10 : Real) * Real.log 11 + A :=
  ⟨11 + 0, height_le_weight_transitive⟩

#check gap_instances_chain
#check region_le_weight_from_gap2
#check height_le_weight_transitive
#check height_le_weight_transitive_exists

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GapConsumerChainActual
end
