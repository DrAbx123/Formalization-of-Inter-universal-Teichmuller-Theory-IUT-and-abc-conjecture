import tmp.sheaf.xif.paper.Mzk1P2DetCoefficientFinalActual
import tmp.sheaf.xif.paper.Mzk1P2WeightedDetFinalActual
import tmp.sheaf.xif.paper.Mzk1P2ArchWeightFinalActual
import tmp.sheaf.xif.paper.Mzk1P2ProductFormulaCancelFinalActual
import tmp.sheaf.xif.paper.Mzk1P2NoDetRankOneActual
import tmp.sheaf.xif.paper.Mzk1GapDetHaarFinalActual
/-! Route 2 summary status -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P2Route2SummaryActual
def route2Rows : List String :=
  [ "det coefficient norm<=1: green", "weighted det nonpos: green",
    "R1.3 alignment: green", "principal arch=count: green",
    "rank-one no-det: conditionally green",
    "general det-Haar: open (SNF composition)" ]
theorem route2Rows_length : route2Rows.length = 6 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P2Route2SummaryActual
end
