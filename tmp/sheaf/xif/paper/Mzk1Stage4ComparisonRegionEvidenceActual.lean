import tmp.sheaf.xif.paper.Mzk1Stage4ComparisonRegionActual

/-! # Mzk1Stage4ComparisonRegionEvidenceActual (stage4 lane; supplementary evidence)

A616 module: further evidence for the concrete comparison region — the measured gap and
its normalized value.  Supplementary only; no canonical file is touched.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ComparisonRegionEvidenceActual

open MeasureTheory
open scoped ENNReal
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ComparisonRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4S1902HullConcreteActual

/-- The measured gap between hull and q-region is `2`. -/
theorem comparison_gap :
    (volume concreteHull.region).toReal -
      (volume qRegionPoint).toReal = 2 := by
  rw [concreteHull_measure, qRegionPoint_measure]
  norm_num

/-- The normalized measured gap is `1`. -/
theorem comparison_gap_normalized :
    ((volume concreteHull.region).toReal -
      (volume qRegionPoint).toReal) / 2 = 1 := by
  rw [concreteHull_measure, qRegionPoint_measure]
  norm_num

/-- The q-region's real measure is zero. -/
theorem qRegion_toReal : (volume qRegionPoint).toReal = 0 := by
  rw [qRegionPoint_measure]
  simp

#check comparison_gap
#check comparison_gap_normalized
#check qRegion_toReal

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ComparisonRegionEvidenceActual
end
