import LeanFormal.IUT.Audit.Status

/-! # S3131 paper route: exact field obligations (data only) -/

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldObligationsActual

def S3131PaperRouteFieldObligations : List String :=
  [ "(b): forall eps>0, forall ABC triple, Height.logHeight1 (abcRationalPoint a c) <= (1+eps) * W.logVolume {pt a b c}",
    "(c): forall eps>0, exists D, forall ABC triple, W.logVolume {pt a b c} <= (1+eps)*arithmeticWeight (abcRationalPoint a c) + W.logVolume W.hull + D",
    "dictionary input for (b): sourceLocalLogDegree additivity + hull MissingConcreteVFormCanonicalReadout readout",
    "arithmetic input for (c): IV section 2 / GenEll strength estimates (not formalized in tree)" ]

theorem S3131PaperRouteFieldObligations_length : S3131PaperRouteFieldObligations.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldObligationsActual