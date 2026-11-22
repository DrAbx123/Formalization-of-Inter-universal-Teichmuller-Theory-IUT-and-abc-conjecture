import tmp.sheaf.xif.paper.Mzk1Stage4ABCGapEstimatesActual
import tmp.sheaf.xif.paper.Mzk1Stage4HeightEstimateActual

/-! # Mzk1Stage4GapStructuralAuditActual (stage4 lane; gap structural audit, log-only)

A632 module: structural/shape audit of the Gap1/Gap2 interface — axiom prints for the
gap structures and their combination, plus the audited registry (log-only).
Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GapStructuralAuditActual

/-- The audited gap-structure theorems. -/
def auditedGapStructures : List String :=
  [ "LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual.combined"
  , "LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual.combined_exists"
  , "LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual.gap1_numeric"
  , "LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual.gap2_numeric"
  , "LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightEstimateActual.height_le_region"
  ]

/-- The gap-structure audit registry has five entries. -/
theorem auditedGapStructures_length : auditedGapStructures.length = 5 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual.combined
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual.combined_exists
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual.gap1_numeric
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual.gap2_numeric
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightEstimateActual.height_le_region

#check auditedGapStructures
#check auditedGapStructures_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GapStructuralAuditActual
