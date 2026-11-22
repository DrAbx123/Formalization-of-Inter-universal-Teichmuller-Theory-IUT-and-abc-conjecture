import LeanFormal.IUT.Audit.Status

/-! # S3131 route: V2-field consumption map (data only) -/

namespace LeanFormal.IUT.XiFPaper.S3131RouteRegionConsumptionMapActual

def S3131RouteRegionConsumptionMap : List (String × String) :=
  [ ("comparisonRegion V2 field", "neutral-region image via reindex-image equality S3139C3ConventionRegionConsumerActual.sourceInd1Convention_reindex_image"),
    ("logShellPoint_mem V2 field", "S3139C3ConventionRegionTransferActual.sourceConventionRegion_transfer + S3139ComparisonRegionNeutralActual.mem_transfer"),
    ("height_le_comparisonRegionVolume V2 field", "heightComparisonFamily_image under named invariance"),
    ("regionVolume_le_normalizedWeight V2 field", "regionVolumeFamily_image under named invariance"),
    ("named residual", "FT.route.comparison-invariance = S3131RouteComparisonInvariance W f; NOT automatic") ]

theorem S3131RouteRegionConsumptionMap_length : S3131RouteRegionConsumptionMap.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.S3131RouteRegionConsumptionMapActual