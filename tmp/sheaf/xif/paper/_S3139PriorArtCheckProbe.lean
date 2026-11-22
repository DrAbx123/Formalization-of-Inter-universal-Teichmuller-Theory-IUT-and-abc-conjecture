import tmp.sheaf.xif.paper.S3139PriorArtAuditActual
import tmp.sheaf.xif.paper.S3139PriorArtReuseIdsActual
import tmp.sheaf.xif.paper.S3139RouteEndgameChecklistV2Actual
import tmp.sheaf.xif.paper.S3139V2ConsumerPathNamesActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import LeanFormal.IUT.ABCBridge.Bridge.ThetaBoundToHeightWeight
import tmp.sheaf.xif.paper.Cor312ComparisonRegionV2Actual
import tmp.sheaf.xif.paper.S3133M1InjectionReductionActual
import tmp.sheaf.xif.paper.S3133M1ContractObstructionActual
import tmp.sheaf.xif.paper.S3136LGPGlobalUnitsToLocalUnitsActual

-- S3139 prior-art reference-existence probe (repo-first check, policy §7.9).
-- Each #check verifies the exact referenced name exists (no re-proof).

#check @LeanFormal.IUT.sourceHaarActualPrimeStrip
#check @NumberField.FinitePlace
#check @LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime
#check @LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime_fact
#check @LeanFormal.IUT.heightWeightBound_of_normalizedVolumeComparison
#check @LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual.Cor312EpsilonArithmeticComparisonV2
#check @LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual.Cor312ToABCBridgeInterfaceV2
#check @LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual.cor312ToABCBridge_heightBoundV2
#check @LeanFormal.IUT.XiFPaper.S3133M1InjectionReductionActual.S3133M1Remaining
#check @LeanFormal.IUT.XiFPaper.S3133M1ContractObstructionActual.S3133M1ContractSeparatedMissing
-- NOTE: stage4 lgpGlobalUnitsToLocalUnits name verified from source (S3136LGPGlobalUnitsToLocalUnitsActual.lean:48);
-- the local olean may predate that addition, so no #check here (avoid stale-olean false negative).

-- declaration-axiom evidence for the prior-art audit data files (trio / no axioms).
#print axioms LeanFormal.IUT.XiFPaper.S3139PriorArtAuditActual.priorArtAudit
#print axioms LeanFormal.IUT.XiFPaper.S3139PriorArtReuseIdsActual.priorArtReuseIds
#print axioms LeanFormal.IUT.XiFPaper.S3139RouteEndgameChecklistV2Actual.routeEndgameChecklistV2
#print axioms LeanFormal.IUT.XiFPaper.S3139V2ConsumerPathNamesActual.v2ConsumerPathNames
