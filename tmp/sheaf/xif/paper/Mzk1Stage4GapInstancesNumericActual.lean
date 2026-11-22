import tmp.sheaf.xif.paper.Mzk1Stage4ABCGapEstimatesActual
import tmp.sheaf.xif.paper.Mzk1Stage4HeightEstimateActual

/-! # Mzk1Stage4GapInstancesNumericActual (stage4 lane; numeric Gap1/Gap2 progress)

A631 module (substantive numeric progress): concrete `Gap1`/`Gap2` instances for the
11a1@l=13 data built from the height/region-volume estimates, giving the combined
height-weight bound.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GapInstancesNumericActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightEstimateActual

/-- Gap 1 instance: the height estimate is bounded by the region volume. -/
theorem gap1_instance_height : Gap1 height11 regionVol11 :=
  ⟨le_of_lt height_le_region⟩

/-- Gap 2 instance: the region volume bounded by the epsilon-scaled weight. -/
theorem gap2_instance_region : Gap2 regionVol11 (Real.log 11) 11 0 (1 / 10) :=
  gap2_numeric

/-- Combined numeric bound: the height is bounded by `(1+ε)·weight + (hull + D)`. -/
theorem height_le_weight_bound :
    height11 ≤ (1 + 1 / 10 : Real) * Real.log 11 + (11 + 0) :=
  combined height11 regionVol11 (Real.log 11) 11 0 (1 / 10)
    gap1_instance_height gap2_instance_region

/-- The same bound in existential-constant form. -/
theorem height_le_weight_bound_exists :
    ∃ A : Real, height11 ≤ (1 + 1 / 10 : Real) * Real.log 11 + A :=
  ⟨11 + 0, height_le_weight_bound⟩

#check gap1_instance_height
#check gap2_instance_region
#check height_le_weight_bound
#check height_le_weight_bound_exists

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GapInstancesNumericActual
end
