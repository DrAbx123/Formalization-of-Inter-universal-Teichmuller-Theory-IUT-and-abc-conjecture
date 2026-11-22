/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1S1902ComparisonRegionActual

/-! # A657: Gap-1 scaling consumer interface (abc; declaration-level, no new objects) -/

/- The mainline triple-dependent scaling model is GREEN.  This file is the abc-side
Gap-1 consumer interface: it exposes the scaling declarations consumed by the
`height_le_normalizedRegionVolume` lane and cross-references our concrete comparison
region.  It introduces no new objects and no new named hypotheses. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ScalingConsumerActual

#check Mzk1PaperComparisonRegionScalingActual.tripleScale
#check Mzk1PaperComparisonRegionScalingActual.paperComparisonRegion
#check Mzk1PaperComparisonRegionScalingActual.paperComparisonRegion_shape
#check Mzk1PaperComparisonRegionScalingActual.TripleDependentComparison
#check Mzk1PaperComparisonRegionScalingActual.abc_of_tripleComparison
#check LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionActual.comparisonRegion_eq_unscaled
#check LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionActual.comparisonRegion_eq_unitRegion_of_mem
#check LeanFormal.IUT.XiFPaper.Mzk1S1902ComparisonRegionActual.qPilot_mem_hull

end LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ScalingConsumerActual
