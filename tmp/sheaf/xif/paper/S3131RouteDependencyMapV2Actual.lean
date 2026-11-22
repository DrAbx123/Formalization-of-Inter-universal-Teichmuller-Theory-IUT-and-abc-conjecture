import LeanFormal.IUT.Audit.Status

/-! # S3131 route: paper-route dependency map V2 (data only) -/

namespace LeanFormal.IUT.XiFPaper.S3131RouteDependencyMapV2Actual

def S3131RouteDependencyMapV2 : List (String × String × String) :=
  [ ("(a) region/point/membership", "READY", "neutral-region image + reindex-image equality + mem_transfer"),
    ("(b) undilated height/dictionary", "PENDING HULL", "MissingConcreteVFormCanonicalReadout + sourceLocalLogDegree dictionary"),
    ("(c) undilated region strength", "GAP 2", "split point bound + unit-region bound; NOT card-P; GenEll-strength unless derived"),
    ("comparison invariance", "NAMED RESIDUAL", "FT.route.comparison-invariance; NOT automatic"),
    ("classification", "CONDITIONAL", "ABC from (b)+(c) only; card P derived by tightness") ]

theorem S3131RouteDependencyMapV2_length : S3131RouteDependencyMapV2.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.S3131RouteDependencyMapV2Actual