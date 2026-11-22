import tmp.sheaf.xif.paper.Mzk1P2ProductFormulaCancelActual
/-! P2 product-formula cancellation final status -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P2ProductFormulaCancelFinalActual
def cancelFinalRows : List String :=
  [ "principal arch = count (green)", "R1.3 = -p2WeightedDetLog (green)",
    "arch source identification missing" ]
theorem cancelFinalRows_length : cancelFinalRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P2ProductFormulaCancelFinalActual
end
