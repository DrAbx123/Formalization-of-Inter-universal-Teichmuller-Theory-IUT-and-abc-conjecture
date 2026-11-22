import LeanFormal.IUT.Audit.Status

/-! # S3131 route: comparison-invariance implementation map (stepxi/abc) - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131RouteInvarianceImplementedActual

def S3131RouteInvarianceImplemented : List (String × String) :=
  [ ("S3139RouteComparisonInvarianceActual.SourceRouteComparisonInvariance", "exact forall S, volume (comparison '' S) = volume S; volume_image/region_volume; sourceV2ComparisonRegion_volume_neutral"),
    ("abc equivalent", "S3135ComparisonMeasureInvariance (S3139ComparisonMeasureInvarianceResidualActual)"),
    ("registry ids", "FT.route.comparison-invariance + FT.route.measure-invariance (S3139RouteRegistryIdsActual.routeOpenResiduals; S3139V2ResidualListActual.v2RouteResiduals)"),
    ("consumption point", "V2 comparisonRegion + membership lemmas feeding height_le_comparisonRegionVolume; region volume must use comparison-invariant data or explicit hypothesis"),
    ("V2 neutral consumer", "S3139ComparisonRegionV2NeutralActual.SourceV2ComparisonRegion.mem_transfer/ofNeutral"),
    ("named M0/M1 compositions", "firstTriangleRouteComposition_of_mainlineM0 / _of_qpilotM1") ]

theorem S3131RouteInvarianceImplemented_length : S3131RouteInvarianceImplemented.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.S3131RouteInvarianceImplementedActual