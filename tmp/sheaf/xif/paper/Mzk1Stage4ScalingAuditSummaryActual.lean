import tmp.sheaf.xif.paper.Mzk1Stage4TripleRegionAlignmentActual
import tmp.sheaf.xif.paper.Mzk1Stage4PaperRegionIdentityObstructionActual
import tmp.sheaf.xif.paper.Mzk1Stage4PaperComparisonRegionScalingDesignActual

/-! # Mzk1Stage4ScalingAuditSummaryActual (stage4 lane; scaling audit, log-only)

A628 module: scaling-chain audit summary — axiom prints for the triple-dependent scaling
objects and the alignment/obstruction theorems, plus the audited registry (log-only).
Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ScalingAuditSummaryActual

/-- The audited scaling-chain theorems. -/
def auditedScalingChain : List String :=
  [ "LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.tripleScale"
  , "LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.paperComparisonRegion_shape"
  , "LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.abc_of_tripleComparison"
  , "LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperComparisonRegionScalingDesignActual.realScaling_region_mono"
  , "LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionActual.identity_region_eq"
  , "LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleRegionAlignmentActual.canonicalScaling_region_eq"
  ]

/-- The scaling-chain audit registry has six entries. -/
theorem auditedScalingChain_length : auditedScalingChain.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.paperComparisonRegion_shape
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.abc_of_tripleComparison
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperComparisonRegionScalingDesignActual.realScaling_region_mono
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionActual.identity_region_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleRegionAlignmentActual.canonicalScaling_region_eq

#check auditedScalingChain
#check auditedScalingChain_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ScalingAuditSummaryActual
