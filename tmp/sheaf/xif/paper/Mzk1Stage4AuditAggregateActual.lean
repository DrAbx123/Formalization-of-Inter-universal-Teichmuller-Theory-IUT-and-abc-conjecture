import tmp.sheaf.xif.paper.Mzk1Stage4TripleAlignmentConsumerActual
import tmp.sheaf.xif.paper.Mzk1Stage4PaperRegionIdentityObstructionActual
import tmp.sheaf.xif.paper.Mzk1Stage4A618AuditProofActual

/-! # Mzk1Stage4AuditAggregateActual (stage4 lane; aggregate audit, log-only)

A626 module: aggregate audit over the A618/A622/A625/A626 chain — axiom prints for the
alignment and conditional-ABC consumers plus the canonical triple-comparison theorems
(log-only evidence).  Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4AuditAggregateActual

/-- The audited A622-A626 theorems. -/
def auditedTripleChain : List String :=
  [ "LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.paperComparisonRegion_shape"
  , "LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.abc_of_tripleComparison"
  , "LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleRegionAlignmentActual.canonicalScaling_region_eq"
  , "LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleAlignmentConsumerActual.stage4_conditional_abc"
  , "LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionActual.identity_region_independent"
  ]

/-- The triple-chain audit registry has five entries. -/
theorem auditedTripleChain_length : auditedTripleChain.length = 5 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.paperComparisonRegion_shape
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.abc_of_tripleComparison
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleRegionAlignmentActual.canonicalScaling_region_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleAlignmentConsumerActual.stage4_conditional_abc
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionActual.identity_region_independent

#check auditedTripleChain
#check auditedTripleChain_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4AuditAggregateActual
