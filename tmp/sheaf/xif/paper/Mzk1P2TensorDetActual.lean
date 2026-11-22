import tmp.sheaf.xif.paper.Mzk1P2TensorDetFactorActual
/-! P2 tensor determinant factor (re-export) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P2TensorDetActual
open LeanFormal.IUT.XiFPaper.Mzk1P2TensorDetFactorActual
def tensorDetRows : List String :=
  [ "p2TensorFieldProduct", "p2TensorFinrank_eq_sum",
    "p2TensorScalarDetFactor", "p2TensorHaarDetTransportMissing" ]
theorem tensorDetRows_length : tensorDetRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P2TensorDetActual
end
