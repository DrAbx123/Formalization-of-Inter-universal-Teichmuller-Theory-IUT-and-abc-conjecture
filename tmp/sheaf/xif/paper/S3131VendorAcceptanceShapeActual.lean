import tmp.sheaf.xif.paper.S3137PaperRouteComparisonDataActual
import tmp.sheaf.xif.paper.S3137VendorMappingActual

/-! # S3131 prior-art reuse: vendor acceptance shapes (lattice) - data only -/

namespace LeanFormal.IUT.XiFPaper.S3131VendorAcceptanceShapeActual

def S3131VendorAcceptanceShape : List (String × String) :=
  [ ("S3137VendorMappingActual", "CorollarySchema mapping: Corollary312ComparisonData/thetaPilot/qPilot/qPilot_positive/corollary312 -> acceptance shape for (b)"),
    ("S3137PaperRouteComparisonDataActual", "local S3137Corollary312ComparisonData.ofQTheta from qTheta comparison + positivity -> acceptance shape for (b)"),
    ("S3137CitationStrengthTableActual / S3137GenEllCorpusAssetActual", "citation strength audit rows + GenEll corpus paths -> documentation reuse"),
    ("S3137PriorArtPaperRouteActual", "lattice prior-art map of route fields -> reuse"),
    ("R1 final pointers", "S3133GaussianModelMapResidualFinalActual (R1 = M1 + M2b); M2a closed evidence; S3137ModelTheaterFamilyActual theater family CLOSED BY REUSE") ]

theorem S3131VendorAcceptanceShape_length : S3131VendorAcceptanceShape.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.S3131VendorAcceptanceShapeActual