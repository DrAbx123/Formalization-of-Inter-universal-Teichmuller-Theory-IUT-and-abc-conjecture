import LeanFormal.IUT.Audit.Status

/-! # S3131 paper route: provable vs GenEll-strength separation (data only) -/

namespace LeanFormal.IUT.XiFPaper.S3131PaperRouteProvableSeparationActual

def S3131PaperRouteProvableNow : List String :=
  [ "S3131PaperRouteSkeletonActual: comparisonRegion/logShellPoint/membership constructed; abcConjecture_of_paperRouteResiduals conditional theorem (card P not a hypothesis)",
    "S3131PaperRouteFieldStatementsActual: exact (b)/(c) family statements",
    "S3131PaperRouteAssemblyActual: PaperRouteResidualData assembly from families",
    "S3131PaperRouteABCBridgeActual: paperRouteABC_of_families (checker CITABLE)",
    "S3131PaperRouteHeightReductionActual: undilated => (b) with dilation bookkeeping",
    "S3131PaperRouteRegionReductionActual: undilated => (c) with dilation bookkeeping" ]

def S3131PaperRouteRemainingStrength : List String :=
  [ "(b) UNDILATED height/dictionary bound for the actual hull interface (hull readout + dictionary files)",
    "(c) UNDILATED IV section 2 arithmetic strength estimate (GenEll; vendor ledger says explicit hypothesis)",
    "concrete W/point instantiation for the actual paper hull (stage4 native data + lgpNativeHaarFamily; hull readout)" ]

theorem S3131PaperRouteProvableNow_length : S3131PaperRouteProvableNow.length = 6 := rfl
theorem S3131PaperRouteRemainingStrength_length : S3131PaperRouteRemainingStrength.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.S3131PaperRouteProvableSeparationActual