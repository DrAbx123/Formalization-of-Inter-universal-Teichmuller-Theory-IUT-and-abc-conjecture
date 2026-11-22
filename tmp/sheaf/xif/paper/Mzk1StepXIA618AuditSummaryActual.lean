import tmp.sheaf.xif.paper.Mzk1StepXIObstructionTripleScaleActual
import tmp.sheaf.xif.paper.Mzk1StepXIComparisonRegionFintypeConsumerActual
import tmp.sheaf.xif.paper.Mzk1StepXITripleDependentScalingActual
import tmp.sheaf.xif.paper.Mzk1StepXIS1902BridgeWiringActual

/-!
# stepxi A618 audit summary (obstruction/comparison)

Read-only machine audit of the A618 obstruction, comparison region, triple scaling,
and bridge interfaces.  No canonical file is modified. -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIObstructionTripleScaleActual.not_mem_tripleScaleRegion_of_not_range
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIComparisonRegionFintypeConsumerActual.stepxi_minimalRegion_fintype_subset
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902BridgeWiringActual.stepxiBridge_heightBound
#check LeanFormal.IUT.XiFPaper.Mzk1StepXITripleDependentScalingActual.uniformToTriple
