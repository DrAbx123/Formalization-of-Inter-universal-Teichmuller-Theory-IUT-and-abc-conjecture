import LeanFormal.IUT.Audit.Status

/-! # S3131 paper-route dependency map (data only) -/

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteDependencyDataActual

def S3131PaperRouteDependencyMap : List (String × String × String) :=
  [ ("(a) comparisonRegion/logShellPoint/membership", "CONSTRUCTED", "S3131PaperRouteSkeletonActual.comparisonOfResiduals"),
    ("(b) height_le_comparisonRegionVolume", "HYPOTHESIS Family", "HeightComparisonFamily; IUT IV Thm 1.10 shape; fed by hull MissingConcreteVFormCanonicalReadout + lgpNativeHaarFamily"),
    ("(c) regionVolume_le_normalizedWeight", "HYPOTHESIS Family", "RegionVolumeFamily; IV section 2 / [GenEll] estimate; equivalent to card P by tightness - must be derived"),
    ("bridge", "ASSEMBLED", "bridgeOfResiduals : Cor312ToABCBridgeInterfaceV2"),
    ("ABC", "CONDITIONAL", "abcConjecture_of_paperRouteResiduals / paperRouteABC_of_families (no card-P hypothesis)") ]

theorem S3131PaperRouteDependencyMap_length :
    S3131PaperRouteDependencyMap.length = 5 := rfl

#check S3131PaperRouteDependencyMap

end LeanFormal.IUT.XiFPaper.S3131PaperRouteDependencyDataActual